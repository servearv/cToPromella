## My current translator.py is:

from __future__ import annotations
from typing import Any, Callable, Dict, Type, List, Optional
from pycparser import c_ast
from .promela_writer import PromelaWriter


# Add this right below your existing imports:
C_TO_PROMELA_TYPE_MAP = {
    'int': 'int',
    'unsigned': 'int',
    'short': 'int',
    'long': 'int',
    'char': 'byte',
    'float': 'int',    # no native float support in Promela
    'double': 'int',
    '_Bool':   'bool',  # <stdbool.h> macro expands to this
    'bool': 'bool',
    'void': 'void',
}

C_SIZEOF_MAP = {
    'int':    4,
    'long':   8,
    'short':  2,
    'char':   1,
    'byte':   1,
    'bool':   1,
    # add more as needed
}

STRUCT_DEFS: dict[str, list[c_ast.Decl]] = {}

C_SPECIAL_CONST = {'NULL': '0'}
PTR_SIZE        = 1          # every pointer is a 1‑byte “address” in our model
MEM_SIZE        = 1024       # size of the synthetic heap


def resolve_type(node: c_ast.Node) -> str:
    """
    Walks pycparser type nodes and returns the Promela type name.
    """
    #If this is an array declaration, the Promela type is just
    #the element type (Promela arrays carry their size in the decl).
    if isinstance(node, c_ast.ArrayDecl):
        return resolve_type(node.type)
    # Strip pointers
    if isinstance(node, c_ast.PtrDecl):
        # return resolve_type(node.type)
        return 'int'
    # Strip out Decl wrappers
    if isinstance(node, c_ast.Decl):
        return resolve_type(node.type)
    # Strip TypeDecl wrappers
    if isinstance(node, c_ast.TypeDecl):
        return resolve_type(node.type)
    
    # --- raw struct references (e.g. from `struct Foo x;`) ---
    #    if we’ve already collected Foo in STRUCT_DEFS, use that name;
    #    otherwise treat it as an opaque int.
    if isinstance(node, c_ast.Struct):
        if node.name and node.name in STRUCT_DEFS:
            return node.name
        return 'int'

    if isinstance(node, c_ast.IdentifierType):
        alias = " ".join(node.names)
        # first try built‐in C→Promela
        for n in node.names:
            if n in C_TO_PROMELA_TYPE_MAP:
                return C_TO_PROMELA_TYPE_MAP[n]
        # then try a struct‐typedef alias
        if alias.startswith("struct "):
            alias = alias.split(" ",1)[1]
        
        if alias in STRUCT_DEFS:
            return alias
        # 4) Otherwise fall back to int
        return 'int'
    # --- fall-back: constants & anything we missed ---
    if isinstance(node, c_ast.Constant):
        return 'byte' if node.type == 'char' else 'int'
    return 'int'

class C2PTranslator:
    _tmp_counter = 0


    def __init__(self) -> None:
        global STRUCT_DEFS
        self.struct_defs = {}
        STRUCT_DEFS = self.struct_defs 
        self._static_map: Dict[str,int] = {}
        self._next_static = 0
        self.w = PromelaWriter()
        self.initialized_vars: set[str] = set()
        self.struct_defs: Dict[str, List[c_ast.Decl]] 
        self._parent_map: dict[c_ast.Node, c_ast.Node] = {}  
        self._skip_set:   set[c_ast.Node] = set()             
        self._heap_var  = "heap_next"   
        self._heap_init = False         
        self.function_return_types: Dict[str,str] = {}
        self.var_types: Dict[str, str] = {}
        self._dispatch: Dict[Type[c_ast.Node], Callable[[c_ast.Node], None]] = {
            c_ast.FileAST: self.t_FileAST,
            c_ast.FuncDef: self.t_FuncDef,
            c_ast.Typedef: self.t_Typedef,
            c_ast.Struct: self.t_Struct,
            c_ast.Compound: self.t_Compound,
            c_ast.Decl: self.t_Decl,
            c_ast.Assignment: self.t_Assignment,
            c_ast.Return: self.t_Return,
            c_ast.Constant: self.t_Constant,
            c_ast.ID: self.t_ID,
            c_ast.BinaryOp: self.t_BinaryOp,
            c_ast.UnaryOp: self.t_UnaryOp,
            c_ast.TernaryOp: self.t_TernaryOp,
            c_ast.If: self.t_If,
            c_ast.While: self.t_While,
            c_ast.For: self.t_For,
            c_ast.Switch: self.t_Switch,
            c_ast.Case: self.generic,
            c_ast.Default: self.generic,
            c_ast.Break: self.t_Break,
            c_ast.FuncCall: self.t_FuncCall,
        }
         
    def _tmp_id(self) -> int:
        self.__class__._tmp_counter += 1
        return self.__class__._tmp_counter
    
    def _annotate_parents(self, root: c_ast.Node) -> None:
        for _, child in root.children():
            self._parent_map[child] = root        # ← store, don’t set attribute
            self._annotate_parents(child)

    def _clean_const(self, c: c_ast.Constant) -> str:
        txt = c.value
        # strip C suffixes
        txt = txt.rstrip('uU').rstrip('lL').rstrip('fF')
        # down-cast floats/doubles to the nearest int
        if c.type in ('float', 'double'):
            txt = str(int(float(txt)))
        func = getattr(self, '_current_func', '')
        if c.type == 'int' and txt in ('0', '1') and 'bool' in func:
            return 'false' if txt == '0' else 'true'
        return txt

    def _alloc_static(self, var: str) -> int:
        """Assign a fixed byte‐offset for each global/struct instance."""
        if var not in self._static_map:
            self._static_map[var] = self._next_static
            # assume 1‑byte “objects” for now
            self._next_static += 1
        return self._static_map[var]

    def _emit_malloc(self, sizeof_str: str) -> str:
        tmp_ptr = f"tmp_malloc_{self._tmp_id()}"
        self.w.write(f"int {tmp_ptr};")
        self.w.write("atomic {"); self.w.enter()
        self.w.write(f"{tmp_ptr} = {self._heap_var};")
        self.w.write(f"{self._heap_var} = {self._heap_var} + {sizeof_str};")
        self.w.exit(); self.w.write("}")
        return tmp_ptr

    def _field_offset(self, field_name: str) -> int:
        """
        Byte‑offset of a named field within any struct we've collected.
        Assumes 1‑byte per field.
        """
        for fields in self.struct_defs.values():
            names = [d.name for d in fields]
            if field_name in names:
                return names.index(field_name)
        raise NotImplementedError(f"Field '{field_name}' not found")

    def _sizeof_value(self, sizeof_node: c_ast.UnaryOp) -> str:
        """
        Compute sizeof(...) in bytes for our model:
        - pointers use PTR_SIZE
        - arrays, primitives use C_SIZEOF_MAP
        """
        target = sizeof_node.expr
        # sizeof(type)
        if isinstance(target, (c_ast.TypeDecl, c_ast.IdentifierType,
                               c_ast.PtrDecl, c_ast.ArrayDecl)):
            ptype = resolve_type(target)
            if isinstance(target, c_ast.PtrDecl):
                return str(PTR_SIZE)
            if ptype in self.struct_defs:
                return str(len(self.struct_defs[ptype])) 
            return str(C_SIZEOF_MAP.get(ptype, 1))
        # sizeof(var)
        if isinstance(target, c_ast.ID):
            if target.name in self._static_map:
                return str(PTR_SIZE)
            ptype = self.var_types.get(target.name, 'int')
            return str(C_SIZEOF_MAP.get(ptype, 1))
        # fallback
        return str(PTR_SIZE)

    def translate(self, node: c_ast.FileAST) -> str:
        self._annotate_parents(node)

        #  #first collect *all* concrete struct definitions -----------
        for ext in node.ext:
            if isinstance(ext, c_ast.Decl) and isinstance(ext.type, c_ast.Struct):
                if ext.type.decls:                       # real definition, not a ref
                    self.struct_defs.setdefault(ext.type.name, ext.type.decls)
            elif isinstance(ext, c_ast.Struct) and ext.decls:
                self.struct_defs.setdefault(ext.name, ext.decls)
        # Next pass: collect struct typedefs
        for ext in node.ext:
            if isinstance(ext, c_ast.Typedef):
                self._visit(ext)
        
        # Second pass: full translation
        self._visit(node)
        return str(self.w)
    
    def t_Typedef(self, node: c_ast.Typedef) -> None:
        """Collect struct typedefs of form: typedef struct { ... } Name;"""
        # if isinstance(node.type.type, c_ast.Struct):
        #     struct = node.type.type
        #     self.struct_defs[node.name] = struct.decls or []
        #     if struct.name is None:
        #         struct.name = node.name
        # only handle typedefs of the form: typedef struct { ... } Name;
        if not isinstance(node.type.type, c_ast.Struct):
            return
        struct = node.type.type
        # A true inline-def comes with .decls; otherwise alias existing named struct
        if struct.decls:
            fields = struct.decls
        else:
            fields = self.struct_defs.get(struct.name, [])
        # record under the new typedef name
        self.struct_defs[node.name] = fields
        # if it really was anonymous, give it the alias name
        if struct.name is None:
            struct.name = node.name

    def t_Struct(self, node: c_ast.Struct) -> None:
        if node.decls is None:        # real forward decl
            return
        if node.name:                 # named definition
            self.struct_defs.setdefault(node.name, node.decls)
        # pure struct literal outside typedef: skip or error
        pass

    def _visit(self, node: c_ast.Node | None) -> None:  
        if node is None:
            return
        handler = self._dispatch.get(type(node), self.generic)
        handler(node)  # type: ignore[arg-type]

    def t_Constant(self, node: c_ast.Constant) -> None:   
        # fall back: render constant as expression + semicolon
        self.w.write(f"{self._clean_const(node)};")

    def t_ID(self, node: c_ast.ID) -> None:   
        self.w.write(f"{node.name};")

    def t_BinaryOp(self, node: c_ast.BinaryOp) -> None: 
        # 1) short-circuit logical AND / OR
        if node.op in ("&&", "||"):
            tmp = f"tmp_log_{self._tmp_id()}"
             # declare a bool temp
            self.w.write(f"bool {tmp};")

            a = self._expr(node.left)
            b = self._expr(node.right)
            if node.op == "&&":
                 # tmp = a && b  →  if a then if b then tmp=true else tmp=false else tmp=false
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {a} ->")
                self.w.enter()
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {b} -> {tmp} = true;")
                self.w.write(f":: else ->    {tmp} = false;")
                self.w.exit(); self.w.write("fi;")
                self.w.exit()
                self.w.write(":: else ->")
                self.w.enter()
                self.w.write(f"{tmp} = false;")
                self.w.exit()
                self.w.exit(); self.w.write("fi;")
            else:
                # tmp = a || b
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {a} -> {tmp} = true;")
                self.w.write(":: else ->")
                self.w.enter()
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {b} -> {tmp} = true;")
                self.w.write(f":: else ->    {tmp} = false;")
                self.w.exit(); self.w.write("fi;")
                self.w.exit()
                self.w.exit(); self.w.write("fi;")

            return
        # 2) all other binary ops (including ^, &, |, +, -, *, /, %, <<, >>)
        self.w.write(f"{self._expr(node)};")

    def t_UnaryOp(self, node: c_ast.UnaryOp) -> None:    
        op   = node.op
        expr = node.expr
        if op in ("++", "p++"):
            var = self._expr(expr)
            step = PTR_SIZE if self.var_types.get(node.expr.name)=='int' else 1
            # emit a = a + 1;
            self.w.write(f"{var} = {var} + {step};")
        elif op in ("--", "p--"):
            var = self._expr(expr)
            step = PTR_SIZE if self.var_types.get(node.expr.name)=='int' else 1
            # emit a = a - 1;
            self.w.write(f"{var} = {var} - {step};")
        else:
            # everything else (e.g. !a, ~a) can stay an expression‐statement
            self.w.write(f"{self._expr(node)};")

    def t_TernaryOp(self, node: c_ast.TernaryOp) -> None:
        # 1) pick a result type by resolving both branches
        t_true  = resolve_type(node.iftrue) or int
        t_false = resolve_type(node.iffalse) or int
        result_type = t_true if t_true == t_false else 'int'

        # 2) make a fresh temp of that type
        tmp = f"tmp_ternary_{self._tmp_id()}"
        self.w.write(f"{result_type} {tmp};")

        # 3) desugar into if/fi assigning into tmp
        cond = self._expr(node.cond)
        self.w.write("if"); self.w.enter()
        self.w.write(f":: {cond} -> {tmp} = {self._expr(node.iftrue)};")
        self.w.write(f":: else -> {tmp} = {self._expr(node.iffalse)};")
        self.w.exit(); self.w.write("fi;")

        # 4) record tmp as the value of the expression
        #    callers of t_TernaryOp should return this name
        return tmp

    def t_FileAST(self, node: c_ast.FileAST) -> None:
        self.w.write(f"byte mem[{MEM_SIZE}];")
        if not self._heap_init:
            self.w.write("int heap_next = 0;")
            self._heap_init = True

        # 1st pass – typedefs
        for ext in node.ext:
            if isinstance(ext, c_ast.Typedef):
                self._visit(ext)

        # emit typedef-ed structs
        for name, fields in self.struct_defs.items():
            self.w.write(f"typedef {name} {{")
            self.w.enter()
            for decl in fields:
                ftype = resolve_type(decl)
                self.w.write(f"{ftype} {decl.name};")
            self.w.exit()
            self.w.write("}")

        # does the file contain an explicit main() ?
        has_main = any(isinstance(ext, c_ast.FuncDef) and ext.decl.name == "main"
                    for ext in node.ext)

        # 2nd pass – translate everything
        for ext in node.ext:
            if not isinstance(ext, c_ast.Typedef):
                self._visit(ext)

        # choose entry-point and build an argument list of zeros
        entry_name = "main"
        extra_args = []            # ints we will pass after the return channel

        if not has_main:
            for ext in node.ext:            # first function in the file
                if isinstance(ext, c_ast.FuncDef):
                    entry_name = ext.decl.name
                    args = getattr(ext.decl.type, "args", None)
                    if args and args.params:
                        # skip the implicit OUT chan → count just the int params
                        extra_args = ["0"] * len(args.params)
                    break
        
        ##Another way to do this is to use the function signature
        # self.w.write("init {")
        # self.w.enter()

        # if entry_ret_type != 'void':
        #     self.w.write(f"chan ret_entry = [0] of {{ {entry_ret_type} }};")

        # # build argument list
        # arg_str = ", ".join(["ret_entry"] * (entry_ret_type != 'void') + extra_args)
        # self.w.write(f"run {entry_name}({arg_str});")

        # if entry_ret_type != 'void':
        #     self.w.write("ret_entry ? 0;")

        # self.w.exit()
        # self.w.write("}")

        # ----- init -----
        self.w.write("init {")
        self.w.enter()
        entry_ret_type = self.function_return_types.get(entry_name, 'int')
        call_args: List[str] = []
        # if entry_ret_type != 'void':
        #     call_args.append(f"chan ret_entry = [0] of {{ {entry_ret_type} }}")
        # call_args += extra_args
        # self.w.write(f"run {entry_name}({', '.join(call_args)})")
        # if entry_ret_type != 'void':
        #     self.w.write("ret_entry ? 0;")
        if entry_ret_type != 'void':
            self.w.write(f"chan ret_entry = [0] of {{ {entry_ret_type} }};")
            self.w.write(f"run {entry_name}(ret_entry{(', ' + ', '.join(extra_args)) if extra_args else ''})")
            self.w.write("ret_entry ? 0;")
        else:
            self.w.write(f"run {entry_name}({', '.join(extra_args)})")

        self.w.exit()
        self.w.write("}")

    def t_FuncDef(self, node: c_ast.FuncDef) -> None:
        fname     = node.decl.name
        ret_type = resolve_type(node.decl.type.type) 
        self.function_return_types[fname] = ret_type
        self._current_func = fname

        args_node = getattr(node.decl.type, "args", None)

        # ---------- gather ordinary parameters ----------
        params: List[str] = []
        if args_node and args_node.params:
            for p in args_node.params:
                # skip unnamed (e.g. function-pointer placeholders)
                if not getattr(p, "name", None):
                    continue

                # 1) array parameter: preserve [size]
                if isinstance(p.type, c_ast.ArrayDecl):
                    elem_type = resolve_type(p.type.type)
                    size_expr = self._expr(p.type.dim)
                    params.append(f"{elem_type} {p.name}[{size_expr}]")
                    # track so ID resolution works for arr in the body
                    self.var_types[p.name] = f"{elem_type}[{size_expr}]"
                else:
                    # 2) scalar *or* pointer parameter.
                    if isinstance(p.type, c_ast.PtrDecl):
                       # real C pointer → Promela int
                        params.append(f"int {p.name}")
                        self.var_types[p.name] = 'int'
                    else:
                        ptype = resolve_type(p)
                        params.append(f"{ptype} {p.name}")
                        self.var_types[p.name] = ptype
        # ---------- OUT channel ----------
        # only add a return channel if not void
        if ret_type != 'void':
            params.insert(0, f"chan ret = [0] of {{ {ret_type} }}")
# otherwise, leave params as-is (just the ordinary parameters)

        self._current_ret = "ret"           # variable used inside the body
        self._exit_label  = f"end_{fname}"

        # ---------- emit proctype ----------
        # filter out any falsy entries (just in case)
        param_list = "; ".join(p for p in params if p)
        self.w.write(f"proctype {fname}({param_list}) "+"{")
        self.w.enter()
        self._visit(node.body)              # translate body
        self.w.write(f"{self._exit_label}: skip;")
        self.w.exit()
        self.w.write("}")
        
        del self._current_func
        del self._current_ret
        del self._exit_label

    def t_Compound(self, node: c_ast.Compound) -> None:
        for stmt in node.block_items or []:
            if stmt in self._skip_set:      # already output inside an ELSE guard
                continue
            self._visit(stmt)

    def t_Decl(self, node: c_ast.Decl) -> None:

        if node.name is None and isinstance(node.type, c_ast.Struct):
        # still record the fields, in case we haven't done so yet
            self.t_Struct(node.type)
            return

        # handle struct InitList with designated initializers
        if isinstance(node.init, c_ast.InitList) \
           and isinstance(node.type, c_ast.TypeDecl) \
           and isinstance(node.type.type, c_ast.Struct):
            structname = node.type.type.name
            # 1) declare the variable
            self.w.write(f"{structname} {node.name};")
            self.var_types[node.name] = structname
            # 2) desugar each .field = expr
            from pycparser.c_ast import NamedInitializer
            for init in node.init.exprs:
                if isinstance(init, NamedInitializer):
                    field = init.name[0].name
                    val   = self._expr(init.expr)
                    self.w.write(f"{node.name}.{field} = {val};")
            return
        if node.name is None \
            and isinstance(node.type, c_ast.TypeDecl) \
            and isinstance(node.type.type, c_ast.Struct):
            self.t_Struct(node.type.type)
            return
        name = node.name
        tp=node.type
        # ---- pointer declarations: T *p; ----
        if isinstance(tp, c_ast.PtrDecl):
            # store as an int address
            self.var_types[name] = 'int'
            init = f" = {self._expr(node.init)}" if node.init else ""
            self.w.write(f"int {name}{init};")
            return
        if isinstance(tp, c_ast.ArrayDecl):
            elem_type = resolve_type(tp.type)
            length = self._expr(tp.dim)
            self.var_types[name] = f"{elem_type}[{length}]"  # track for ID checks
            self.w.write(f"{elem_type} {name}[{length}];")
            
            init = node.init
            if isinstance(init, c_ast.InitList):
                for idx, expr in enumerate(init.exprs):
                    val = self._expr(expr)
                # arr[idx] = val;
                    self.w.write(f"{name}[{idx}] = {val};")
            return
        # struct variables
        if isinstance(tp, c_ast.TypeDecl) and isinstance(tp.type, c_ast.Struct):
            structname = tp.type.name
            self.w.write(f"{structname} {name};")
            # record that `name` is of struct type
            self.var_types[name] = structname
            return
        
        if isinstance(tp, c_ast.TypeDecl) and isinstance(tp.type, c_ast.IdentifierType):
            alias = " ".join(tp.type.names)
            if alias in self.struct_defs:          # it *is* a struct alias
                self.w.write(f"{alias} {name};")
                self.var_types[name] = alias
                return

        # scalar or other simple types
        ptype = resolve_type(node)      # <— get Promela type
        self.var_types[name] = ptype

        # special‐case: prefix/postfix ++ or -- in the initializer
        if isinstance(node.init, c_ast.UnaryOp) \
           and node.init.op in ("++", "p++", "++p", "--", "p--", "--p"):
            var = node.init.expr.name
            if node.init.op in ("++", "p++"):
                # emulate   int name = ++var;
                self.w.write(f"{var} = {var} + 1;")
                self.w.write(f"{ptype} {name} = {var};")
            else:
                # emulate   int name = var--;
                self.w.write(f"{ptype} {name} = {var};")
                self.w.write(f"{var} = {var} - 1;")
            return
        
        # special‐case: ternary in initializer
        if isinstance(node.init, c_ast.TernaryOp):
            # let t_TernaryOp emit the temp and its if/fi,
            # then bind that temp into our declaration.
            tmp = self.t_TernaryOp(node.init)
            self.w.write(f"{ptype} {node.name} = {tmp};")
            return

        # fallback: any other initializer or none
        init = ""
        if node.init:
            init = f" = {self._expr(node.init)}"
            self.initialized_vars.add(name)
        self.w.write(f"{ptype} {name}{init};")

        # --- synthetic heap support for globals ---------------------------------
        parent = self._parent_map.get(node)
        if isinstance(parent, c_ast.FileAST):              # only file-scope vars
            addr = self._alloc_static(name)               # allocate (or reuse) byte
            self.w.write(f"mem[{addr}] = {name};")

    def t_Assignment(self, node: c_ast.Assignment) -> None:
        left = self._expr(node.lvalue)
        right = self._expr(node.rvalue)
        op = node.op

    # Special case: struct assignment
        if op == '=' and isinstance(node.lvalue, c_ast.ID) and isinstance(node.rvalue, c_ast.ID):
            lvar = node.lvalue.name
            rvar = node.rvalue.name
            ltype = self.var_types.get(lvar)
            if ltype in self.struct_defs:
                for field in self.struct_defs[ltype]:
                    fname = field.name
                    self.w.write(f"{lvar}.{fname} = {rvar}.{fname};")
                return

        # Otherwise normal
        if op == "=":
            self.w.write(f"{left} = {right};")
        else:
            # desugar any compound-assignment X op= Y → X = X op Y
            base_op = op[:-1]  # e.g. '+=' → '+'
            self.w.write(f"{left} = {left} {base_op} {right};")
            
    def t_Return(self, node: c_ast.Return) -> None:
        """
        Emit a block that:
        1. evaluates the return expression (any declarations stay legal),
        2. sends the result on the OUT channel,
        3. jumps to the common exit label.
        """
        out_chan = getattr(self, "_current_ret", "ret")

        # open a local scope
        self.w.write("{")
        self.w.enter()

        # 1) generate code for the expression
        value_expr = "0"
        if node.expr:
            value_expr = self._expr(node.expr)   # this may emit declarations

        # 2) send the value
        ret_type = self.function_return_types.get(self._current_func, 'int')
        if ret_type != 'void':
            self.w.write(f"{out_chan} ! {value_expr};")

        # 3) leave the function
        self.w.write(f"goto {self._exit_label};")

        # close scope
        self.w.exit()
        self.w.write("}")

    def t_If(self, node: c_ast.If) -> None:
        cond = self._expr(node.cond)
        self.w.write("if")
        self.w.enter()

        # --- THEN guard ----------------------------------------------------
        self.w.write(f":: {cond} ->")
        self.w.enter()
        self._visit(node.iftrue)
        self.w.exit()

        # --- ELSE guard ----------------------------------------------------
        self.w.write(":: else ->")
        self.w.enter()

        if node.iffalse:
            self._visit(node.iffalse)
        else:
            # pull an immediate following `return` (C tail-return pattern)
            parent = self._parent_map.get(node)
            if isinstance(parent, c_ast.Compound):
                sibs = parent.block_items or []
                idx  = sibs.index(node)
                if idx + 1 < len(sibs) and isinstance(sibs[idx + 1], c_ast.Return):
                    self._visit(sibs[idx + 1])
                    self._skip_set.add(sibs[idx + 1])   # remember we printed it
        self.w.exit()

        self.w.exit()
        self.w.write("fi")

    def t_While(self, node: c_ast.While) -> None:
        is_infinite = (isinstance(node.cond, c_ast.Constant) and node.cond.value in ("1", "true"))
        cond = self._expr(node.cond)
        self.w.write("do")
        self.w.enter()
        self.w.write(f":: {cond} ->")
        self.w.enter(); self._visit(node.stmt); self.w.exit()
        if not is_infinite:
            self.w.write(":: else -> break;")
        self.w.exit()
        self.w.write("od;")

    def t_For(self, node: c_ast.For) -> None:
        # initialization
        if node.init:
            # only emit the init assignment if it wasn't already set by the declaration
            if isinstance(node.init, c_ast.Assignment) \
                and isinstance(node.init.lvalue, c_ast.ID) \
                and node.init.lvalue.name in self.initialized_vars:
                    pass
            else:
                self._visit(node.init)

        cond = self._expr(node.cond) if node.cond else 'true'
        self.w.write("do")
        self.w.enter()
        self.w.write(f":: {cond} ->")
        self.w.enter()
        # loop body
        self._visit(node.stmt)
        # increment handling: support ++ and general expression
        if node.next:
            if isinstance(node.next, c_ast.UnaryOp) and node.next.op == 'p++':
                # post-increment: x++ → x = x + 1;
                var = node.next.expr.name
                self.w.write(f"{var} = {var} + 1;")
            elif isinstance(node.next, c_ast.UnaryOp) and node.next.op == 'p--':
                var = node.next.expr.name
                self.w.write(f"{var} = {var} - 1;")
            else:
                incr = self._expr(node.next)
                self.w.write(f"{incr};")
        self.w.exit()
        self.w.write(":: else -> break;")
        self.w.exit()
        self.w.write("od;")

    def t_Switch(self, node: c_ast.Switch) -> None:
        var = self._expr(node.cond)
        # collect cases
        cases: List[tuple[str, List[c_ast.Node]]] = []
        default_body: Optional[List[c_ast.Node]] = None
        for stmt in node.stmt.block_items or []:
            if isinstance(stmt, c_ast.Case):
                val = self._expr(stmt.expr)
                cases.append((val, stmt.stmts or []))
            elif isinstance(stmt, c_ast.Default):
                default_body = stmt.stmts or []
        # emit if-chain
        self.w.write("if")
        self.w.enter()
        for val, stmts in cases:
            self.w.write(f":: ({var} == {val}) ->")
            self.w.enter()
            for s in stmts:
                self._visit(s)
            self.w.exit()
        if default_body is not None:
            self.w.write(":: else ->")
            self.w.enter()
            for s in default_body:
                self._visit(s)
            self.w.exit()
        self.w.exit()
        self.w.write("fi")

    def t_Break(self, node: c_ast.Break) -> None:
        self.w.write("break;")

    def t_FuncCall(self, node: c_ast.FuncCall) -> str:
        """
        Emit Promela code for a function call and return the name of the
        temporary that holds the result.  Declarations are produced inline
        (no extra braces), so the temp is still visible to the caller.
        """

        # ---- callee --------------------------------------------------------
        fname = node.name.name if isinstance(node.name, c_ast.ID) else "UNKNOWN"
        if fname in ('malloc', 'free'):
            # already expanded in _expr – nothing more to generate
            return None


        # ---- actual arguments ---------------------------------------------
        actuals: List[str] = []
        if node.args:
            for e in node.args.exprs:
                actuals.append(self._expr(e))
        ret_type = self.function_return_types.get(fname, 'int')
        if ret_type == 'void':
        # just run, no channel or temp
            arg_str = ", ".join(actuals)
            self.w.write(f"run {fname}({arg_str});")
        else:
            ret_chan = f"ret_{fname}_{self._tmp_id()}"
            tmp_var  = f"tmp_{fname}_{self._tmp_id()}"
            self.w.write(f"chan {ret_chan} = [0] of {{ {ret_type} }};")
            self.w.write(f"{ret_type} {tmp_var};")
            arg_str = ", ".join([ret_chan] + actuals)
            self.w.write(f"run {fname}({arg_str});")
            self.w.write(f"{ret_chan} ? {tmp_var};")
            return tmp_var
          
    # def _expr(self, node: c_ast.Node) -> str:
    #     if isinstance(node, c_ast.ID):
    #         assert node.name in self.var_types, f"Unknown var {node.name}"
    #         return node.name
    #     if isinstance(node, c_ast.Constant):
    #         return node.value
    #     if isinstance(node, c_ast.StructRef):
    #         base = self._expr(node.name)
    #         field = node.field.name
    #         return f"{base}.{field}"
    #     if isinstance(node, c_ast.BinaryOp):
    #         left = self._expr(node.left)
    #         right= self._expr(node.right)
    #         return f"({left} {node.op} {right})"
    #     if isinstance(node, c_ast.UnaryOp) and node.op == "sizeof":
    #         # node.expr might be a type or an expression
    #         if isinstance(node.expr, (c_ast.TypeDecl, c_ast.IdentifierType, c_ast.PtrDecl, c_ast.ArrayDecl)):
    #             ptype = resolve_type(node.expr)
    #         else:
    #             # sizeof expr: look up the var’s type you tracked
    #             name = node.expr.name  # assume simple ID
    #             ptype = self.var_types.get(name, 'int')
    #         return str(C_SIZEOF_MAP.get(ptype, 1))
    #     if isinstance(node, c_ast.UnaryOp) and node.op != "sizeof":
    #         return f"({node.op}{self._expr(node.expr)})"
    #     if isinstance(node, c_ast.TernaryOp):
    #         tmp_name = self.t_TernaryOp(node)
    #         return tmp_name
    #     if isinstance(node, c_ast.ArrayRef):
    #         # node.name is the array, node.subscript is the index
    #         base = self._expr(node.name)
    #         idx  = self._expr(node.subscript)
    #         return f"{base}[{idx}]"
    #     if isinstance(node, c_ast.FuncCall):
    #         # the helper above now *returns* the variable that holds the value
    #         res = self.t_FuncCall(node)
    #         return res if res is not None else ""
    #     raise NotImplementedError(f"Expr not supported: {type(node)}")

    def _expr(self, node: c_ast.Node) -> str:
        if isinstance(node, c_ast.ID) and node.name in self._static_map:
            return f"mem[{self._static_map[node.name]}]"

        if isinstance(node, c_ast.TernaryOp):
            # t_TernaryOp emits the declarations and returns the temp name
            return self.t_TernaryOp(node)
        if isinstance(node, c_ast.ID) and node.name in C_SPECIAL_CONST:
            return C_SPECIAL_CONST[node.name]

        # address-of: &x  or  &arr[i]
        if isinstance(node, c_ast.UnaryOp) and node.op == '&':
            tgt = node.expr
            if isinstance(tgt, c_ast.ID):
                return str(self._alloc_static(tgt.name))
            if isinstance(tgt, c_ast.ArrayRef):
                base = self._expr(tgt.name)
                idx  = self._expr(tgt.subscript)
                return f"({base} + {idx})"
            raise NotImplementedError("& on complex expr")

        # dereference: *p
        if isinstance(node, c_ast.UnaryOp) and node.op == '*':
            ptr = self._expr(node.expr)
            return f"mem[{ptr}]"

        # sizeof(...)
        if isinstance(node, c_ast.UnaryOp) and node.op == 'sizeof':
            return self._sizeof_value(node)

        # pointer arithmetic & compound: +, -, +=, -=
        if isinstance(node, c_ast.BinaryOp) and node.op in ('+', '-', '+=', '-='):
            L = self._expr(node.left)
            R = self._expr(node.right)
            return f"({L} {node.op} {R})"

        # struct member: s.f or p->f
        if isinstance(node, c_ast.StructRef):
            fname = node.field.name
            if node.type == '->':                 # pointer → synthetic heap
                off  = self._field_offset(fname)
                base = self._expr(node.name)
                return f"mem[{base} + {off}]"
            # value struct → real field access
            base = self._expr(node.name)
            return f"{base}.{fname}"
        # array indexing
        if isinstance(node, c_ast.ArrayRef):
            base = self._expr(node.name)
            idx  = self._expr(node.subscript)
            # if base is a pointer, treat as mem[base+idx]
            if getattr(node.name, 'name', None) in self.var_types and \
               self.var_types[node.name.name] == 'int':
                return f"mem[{base} + {idx}]"
            return f"{base}[{idx}]"

        # cast: (T*)expr  → no-op on address
        if isinstance(node, c_ast.Cast):
            return self._expr(node.expr)

        # fall back to your existing cases:
        if isinstance(node, c_ast.ID):
            assert node.name in self.var_types
            return node.name
        if isinstance(node, c_ast.Constant):
            return self._clean_const(node)
        if isinstance(node, c_ast.BinaryOp):
            L = self._expr(node.left)
            R = self._expr(node.right)
            return f"({L} {node.op} {R})"
        if isinstance(node, c_ast.UnaryOp):
            # pointer increments/decrements
            if node.op in ('p++','++') and isinstance(node.expr, c_ast.ID) and \
               self.var_types.get(node.expr.name) == 'int':
                return f"{node.expr.name} = {node.expr.name} + {PTR_SIZE}"
            if node.op in ('p--','--') and isinstance(node.expr, c_ast.ID) and \
               self.var_types.get(node.expr.name) == 'int':
                return f"{node.expr.name} = {node.expr.name} - {PTR_SIZE}"
            # return f"({node.op}{self._expr(node.expr)})"   ###########################################
            inner = self._expr(node.expr)
            op = node.op
            # pycparser:  'p++' / 'p--'  =>  postfix
            if op == "p++":
                return f"({inner}++)"
            if op == "p--":
                return f"({inner}--)"
            return f"({op}{inner})" 
        if isinstance(node, c_ast.FuncCall):
            name_id = node.name.name if isinstance(node.name, c_ast.ID) else ""
            if name_id == 'malloc':
                sizeof_arg = node.args.exprs[0]
                size_s     = self._expr(sizeof_arg)
                return self._emit_malloc(size_s)
            if name_id == 'free':
                ptr = self._expr(node.args.exprs[0])
                self.w.write(f"/* free({ptr}); */")
                return ""
            # default handling for other function calls
            tmp = self.t_FuncCall(node)
            return tmp or ""
        
        if isinstance(node, c_ast.TernaryOp):
            # emits the tmp variable and Promela `if…fi` and returns its name
            return self.t_TernaryOp(node)
        


        raise NotImplementedError(f"Expr not supported: {type(node)}")

    def generic(self, node: c_ast.Node, *args: Any, **kw: Any) -> None:
        raise NotImplementedError(f"No handler for {type(node)}")




