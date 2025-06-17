from __future__ import annotations
from typing import Any, Callable, Dict, Type, List, Optional
from pycparser import c_ast
from pycparser.c_ast import NamedInitializer
from .promela_writer import PromelaWriter

# Mapping of C types to Promela types
C_TO_PROMELA_TYPE_MAP = {
    'int': 'int',
    'unsigned': 'int',
    'short': 'int',
    'long': 'int',
    'char': 'byte',
    'float': 'int',
    'double': 'int',
    '_Bool': 'bool',
    'bool': 'bool',
    'void': 'void',
}

# Mapping of C types to their sizes in bytes
C_SIZEOF_MAP = {
    'int': 4,
    'long': 8,
    'short': 2,
    'char': 1,
    'byte': 1,
    'bool': 1,
}

# Mapping of C types to their sizes in bytes for Promela
STRUCT_DEFS: dict[str, list[c_ast.Decl]] = {}
C_SPECIAL_CONST = {'NULL': '0'}
PTR_SIZE = 1
MEM_SIZE = 1024

# resolve_type function to determine the type of a node
# This function is used to resolve the type of a node in the AST
def resolve_type(node: c_ast.Node) -> str:
    if isinstance(node, c_ast.ArrayDecl):
        return resolve_type(node.type)
    if isinstance(node, c_ast.PtrDecl):
        return 'int'
    if isinstance(node, c_ast.Decl):
        return resolve_type(node.type)
    if isinstance(node, c_ast.TypeDecl):
        return resolve_type(node.type)
    if isinstance(node, c_ast.Struct):
        if node.name and node.name in STRUCT_DEFS:
            return node.name
        return 'int'
    if isinstance(node, c_ast.IdentifierType):
        alias = " ".join(node.names)
        for n in node.names:
            if n in C_TO_PROMELA_TYPE_MAP:
                return C_TO_PROMELA_TYPE_MAP[n]
        if alias.startswith("struct "):
            alias = alias.split(" ", 1)[1]
        if alias in STRUCT_DEFS:
            return alias
        return 'int'
    if isinstance(node, c_ast.Constant):
        return 'byte' if node.type == 'char' else 'int'
    return 'int'


# translator class to convert C code to Promela
class C2PTranslator:
    _tmp_counter = 0

    # Constructor to initialize the translator
    # It sets up the necessary mappings and initializes the Promela writer
    def __init__(self) -> None:
        global STRUCT_DEFS
        self.struct_defs = {}
        STRUCT_DEFS = self.struct_defs
        self._static_map: Dict[str, int] = {}
        self._next_static = 0
        self.w = PromelaWriter()
        self.initialized_vars: set[str] = set()
        
        self.struct_defs: Dict[str, List[c_ast.Decl]] 
        self._parent_map: dict[c_ast.Node, c_ast.Node] = {}
        self._skip_set: set[c_ast.Node] = set()
        self._heap_var = "heap_next"
        self._heap_init = False
        self.function_return_types: Dict[str, str] = {}
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
    
    # Function to generate a temporary ID for variables
    def _tmp_id(self) -> int:
        self.__class__._tmp_counter += 1
        return self.__class__._tmp_counter
    
    # Function to annotate parent nodes in the AST
    def _annotate_parents(self, root: c_ast.Node) -> None:
        for _, child in root.children():
            self._parent_map[child] = root
            self._annotate_parents(child)

    # Function to clean constant values
    def _clean_const(self, c: c_ast.Constant) -> str:
        txt=c.value
        txt = txt.rstrip('uU').rstrip('lL').rstrip('fF')
        if c.type in ('float', 'double'):
            txt = str(int(float(txt)))
        func = getattr(self, '_current_func', '')
        if c.type == 'int' and txt in ('0', '1') and 'bool' in func:
            return 'false' if txt == '0' else 'true'
        return txt

    # Function to allocate static variables
    def _alloc_static(self, var: str) -> int:
        if var not in self._static_map:
            self._static_map[var] = self._next_static
            self._next_static += 1
        return self._static_map[var]

    # Function to emit malloc statements
    def _emit_malloc(self, sizeof_str: str) -> str:
        tmp_ptr = f"tmp_malloc_{self._tmp_id()}"
        self.w.write(f"int {tmp_ptr};")
        self.w.write("atomic {"); self.w.enter()
        self.w.write(f"{tmp_ptr} = {self._heap_var};")
        self.w.write(f"{self._heap_var} = {self._heap_var} + {sizeof_str};")
        self.w.exit(); self.w.write("}")
        return tmp_ptr

    # Function to get the offset of a field in a struct
    def _field_offset(self, field_name: str) -> int:
        for fields in self.struct_defs.values():
            names = [d.name for d in fields]
            if field_name in names:
                return names.index(field_name)
        raise NotImplementedError(f"Field '{field_name}' not found")

    # Function to get the size of a value
    def _sizeof_value(self, sizeof_node: c_ast.UnaryOp) -> str:
        target = sizeof_node.expr
        if isinstance(target, (c_ast.TypeDecl, c_ast.IdentifierType,
                               c_ast.PtrDecl, c_ast.ArrayDecl)):
            ptype = resolve_type(target)
            if isinstance(target, c_ast.PtrDecl):
                return str(PTR_SIZE)
            if ptype in self.struct_defs:
                return str(len(self.struct_defs[ptype]))
            return str(C_SIZEOF_MAP.get(ptype, 1))
        if isinstance(target, c_ast.ID):
            if target.name in self._static_map:
                return str(PTR_SIZE)
            ptype = self.var_types.get(target.name, 'int')
            return str(C_SIZEOF_MAP.get(ptype, 1))
        return str(PTR_SIZE)

    # Function to translate the AST to Promela code
    def translate(self, node: c_ast.FileAST) -> str:
        self._annotate_parents(node)
        for ext in node.ext:
            if isinstance(ext, c_ast.Decl) and isinstance(ext.type, c_ast.Struct) and ext.type.decls:
                self.struct_defs.setdefault(ext.type.name, ext.type.decls)
            elif isinstance(ext, c_ast.Struct) and ext.decls:
                self.struct_defs.setdefault(ext.name, ext.decls)
        for ext in node.ext:
            if isinstance(ext, c_ast.Typedef):
                self._visit(ext)
        self._visit(node)
        return str(self.w)

    # Function to handle typedef nodes
    def t_Typedef(self, node: c_ast.Typedef) -> None:
        if not isinstance(node.type.type, c_ast.Struct):
            return
        struct = node.type.type
        fields = struct.decls if struct.decls else self.struct_defs.get(struct.name, [])
        self.struct_defs[node.name] = fields
        if struct.name is None:
            struct.name = node.name

    # Function to handle struct nodes
    def t_Struct(self, node: c_ast.Struct) -> None:
        if node.decls is None:
            return
        if node.name:
            self.struct_defs.setdefault(node.name, node.decls)

    # Function to visit nodes in the AST
    def _visit(self, node: c_ast.Node | None) -> None:
        if node is None:
            return
        handler = self._dispatch.get(type(node), self.generic)
        handler(node)

    # Function to handle constant nodes
    def t_Constant(self, node: c_ast.Constant) -> None:
        self.w.write(f"{self._clean_const(node)};")

    # Function to handle ID nodes
    def t_ID(self, node: c_ast.ID) -> None:
        self.w.write(f"{node.name};")

    # Function to handle binary operations
    def t_BinaryOp(self, node: c_ast.BinaryOp) -> None:
        if node.op in ("&&", "||"):
            tmp = f"tmp_log_{self._tmp_id()}"
            self.w.write(f"bool {tmp};")
            a = self._expr(node.left)
            b = self._expr(node.right)
            if node.op == "&&":
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {a} ->"); self.w.enter()
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {b} -> {tmp} = true;")
                self.w.write(f":: else -> {tmp} = false;")
                self.w.exit(); self.w.write("fi;")
                self.w.exit()
                self.w.write(":: else ->"); self.w.enter()
                self.w.write(f"{tmp} = false;")
                self.w.exit(); self.w.exit(); self.w.write("fi;")
            else:
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {a} -> {tmp} = true;")
                self.w.write(":: else ->"); self.w.enter()
                self.w.write("if"); self.w.enter()
                self.w.write(f":: {b} -> {tmp} = true;")
                self.w.write(f":: else -> {tmp} = false;")
                self.w.exit(); self.w.write("fi;")
                self.w.exit(); self.w.exit(); self.w.write("fi;")
            return
        self.w.write(f"{self._expr(node)};")

    # Function to handle unary operations
    def t_UnaryOp(self, node: c_ast.UnaryOp) -> None:
        op = node.op
        expr = node.expr
        if op in ("++", "p++"):
            var = self._expr(expr)
            step = PTR_SIZE if self.var_types.get(node.expr.name) == 'int' else 1
            self.w.write(f"{var} = {var} + {step};")
        elif op in ("--", "p--"):
            var = self._expr(expr)
            step = PTR_SIZE if self.var_types.get(node.expr.name) == 'int' else 1
            self.w.write(f"{var} = {var} - {step};")
        else:
            self.w.write(f"{self._expr(node)};")

    # Function to handle ternary operations 
    def t_TernaryOp(self, node: c_ast.TernaryOp) -> str:
        t_true = resolve_type(node.iftrue) or int
        t_false = resolve_type(node.iffalse) or int
        result_type = t_true if t_true == t_false else 'int'
        tmp = f"tmp_ternary_{self._tmp_id()}"
        self.w.write(f"{result_type} {tmp};")
        cond = self._expr(node.cond)
        self.w.write("if"); self.w.enter()
        self.w.write(f":: {cond} -> {tmp} = {self._expr(node.iftrue)};")
        self.w.write(f":: else -> {tmp} = {self._expr(node.iffalse)};")
        self.w.exit(); self.w.write("fi;")
        return tmp

    # Function to handle file AST nodes
    def t_FileAST(self, node: c_ast.FileAST) -> None:
        self.w.write(f"byte mem[{MEM_SIZE}];")
        if not self._heap_init:
            self.w.write("int heap_next = 0;")
            self._heap_init = True
        for ext in node.ext:
            if isinstance(ext, c_ast.Typedef):
                self._visit(ext)
        for name, fields in self.struct_defs.items():
            self.w.write(f"typedef {name} {{")
            self.w.enter()
            for decl in fields:
                ftype = resolve_type(decl)
                self.w.write(f"{ftype} {decl.name};")
            self.w.exit()
            self.w.write("}")
        has_main = any(isinstance(ext, c_ast.FuncDef) and ext.decl.name == "main" for ext in node.ext)
        for ext in node.ext:
            if not isinstance(ext, c_ast.Typedef):
                self._visit(ext)
        entry_name = "main"
        extra_args = []
        if not has_main:
            for ext in node.ext:
                if isinstance(ext, c_ast.FuncDef):
                    entry_name = ext.decl.name
                    args = getattr(ext.decl.type, "args", None)
                    if args and args.params:
                        extra_args = ["0"] * len(args.params)
                    break
        self.w.write("init {")
        self.w.enter()
        entry_ret_type = self.function_return_types.get(entry_name, 'int')
        if entry_ret_type != 'void':
            self.w.write(f"chan ret_entry = [0] of {{ {entry_ret_type} }};")
            self.w.write(f"run {entry_name}(ret_entry{(', ' + ', '.join(extra_args)) if extra_args else ''})")
            self.w.write("ret_entry ? 0;")
        else:
            self.w.write(f"run {entry_name}({', '.join(extra_args)})")
        self.w.exit()
        self.w.write("}")

    # Function to handle function definitions
    def t_FuncDef(self, node: c_ast.FuncDef) -> None:
        fname = node.decl.name
        ret_type = resolve_type(node.decl.type.type)
        self.function_return_types[fname] = ret_type
        self._current_func = fname
        args_node = getattr(node.decl.type, "args", None)
        params: List[str] = []
        if args_node and args_node.params:
            for p in args_node.params:
                if not getattr(p, "name", None):
                    continue
                if isinstance(p.type, c_ast.ArrayDecl):
                    elem_type = resolve_type(p.type.type)
                    size_expr = self._expr(p.type.dim)
                    params.append(f"{elem_type} {p.name}[{size_expr}]")
                    self.var_types[p.name] = f"{elem_type}[{size_expr}]"
                else:
                    if isinstance(p.type, c_ast.PtrDecl):
                        params.append(f"int {p.name}")
                        self.var_types[p.name] = 'int'
                    else:
                        ptype = resolve_type(p)
                        params.append(f"{ptype} {p.name}")
                        self.var_types[p.name] = ptype
        if ret_type != 'void':
            params.insert(0, f"chan ret = [0] of {{ {ret_type} }}")
        self._current_ret = "ret"
        self._exit_label = f"end{fname}"
        param_list = "; ".join(params)
        self.w.write(f"proctype {fname}({param_list}) {{")
        self.w.enter()
        self._visit(node.body)
        self.w.write(f"{self._exit_label}: skip;")
        self.w.exit()
        self.w.write("}")
        del self._current_func
        del self._current_ret
        del self._exit_label

    # Function to handle compound statements
    def t_Compound(self, node: c_ast.Compound) -> None:
        for stmt in node.block_items or []:
            if stmt in self._skip_set:
                continue
            self._visit(stmt)

    # Function to handle declarations
    def t_Decl(self, node: c_ast.Decl) -> None:
        if node.name is None and isinstance(node.type, c_ast.Struct):
            self.t_Struct(node.type)
            return
        if isinstance(node.init, c_ast.InitList) and isinstance(node.type, c_ast.TypeDecl) and isinstance(node.type.type, c_ast.Struct):
            structname = node.type.type.name
            self.w.write(f"{structname} {node.name};")
            self.var_types[node.name] = structname
            for init in node.init.exprs:
                if isinstance(init, NamedInitializer):
                    field = init.name[0].name
                    val = self._expr(init.expr)
                    self.w.write(f"{node.name}.{field} = {val};")
            return
        if node.name is None and isinstance(node.type, c_ast.TypeDecl) and isinstance(node.type.type, c_ast.Struct):
            self.t_Struct(node.type.type)
            return
        name = node.name
        tp = node.type
        if isinstance(tp, c_ast.PtrDecl):
            self.var_types[name] = 'int'
            init = f" = {self._expr(node.init)}" if node.init else ""
            self.w.write(f"int {name}{init};")
            return
        if isinstance(tp, c_ast.ArrayDecl):
            elem_type = resolve_type(tp.type)
            length = self._expr(tp.dim)
            self.var_types[name] = f"{elem_type}[{length}]"
            self.w.write(f"{elem_type} {name}[{length}];")
            init = node.init
            if isinstance(init, c_ast.InitList):
                for idx, expr in enumerate(init.exprs):
                    val = self._expr(expr)
                    self.w.write(f"{name}[{idx}] = {val};")
            return
        if isinstance(tp, c_ast.TypeDecl) and isinstance(tp.type, c_ast.Struct):
            structname = tp.type.name
            self.w.write(f"{structname} {name};")
            self.var_types[name] = structname
            return
        if isinstance(tp, c_ast.TypeDecl) and isinstance(tp.type, c_ast.IdentifierType):
            alias = " ".join(tp.type.names)
            if alias in self.struct_defs:
                self.w.write(f"{alias} {name};")
                self.var_types[name] = alias
                return
        ptype = resolve_type(node)
        self.var_types[name] = ptype
        if isinstance(node.init, c_ast.UnaryOp) and node.init.op in ("++", "p++", "++p", "--", "p--", "--p"):
            var = node.init.expr.name
            if node.init.op in ("++", "p++"):
                self.w.write(f"{var} = {var} + 1;")
                self.w.write(f"{ptype} {name} = {var};")
            else:
                self.w.write(f"{ptype} {name} = {var};")
                self.w.write(f"{var} = {var} - 1;")
            return
        if isinstance(node.init, c_ast.TernaryOp):
            tmp = self.t_TernaryOp(node.init)
            self.w.write(f"{ptype} {node.name} = {tmp};")
            return
        init = f" = {self._expr(node.init)}" if node.init else ""
        if node.init:
            self.initialized_vars.add(name)
        self.w.write(f"{ptype} {name}{init};")
        parent = self._parent_map.get(node)
        if isinstance(parent, c_ast.FileAST):
            addr = self._alloc_static(name)
            self.w.write(f"mem[{addr}] = {name};")

    # Function to handle assignment statements
    def t_Assignment(self, node: c_ast.Assignment) -> None:
        left = self._expr(node.lvalue)
        right = self._expr(node.rvalue)
        op = node.op
        if op == '=' and isinstance(node.lvalue, c_ast.ID) and isinstance(node.rvalue, c_ast.ID):
            lvar = node.lvalue.name
            rvar = node.rvalue.name
            ltype = self.var_types.get(lvar)
            if ltype in self.struct_defs:
                for field in self.struct_defs[ltype]:
                    fname = field.name
                    self.w.write(f"{lvar}.{fname} = {rvar}.{fname};")
                return
        if op == "=":
            self.w.write(f"{left} = {right};")
        else:
            base_op = op[:-1]
            self.w.write(f"{left} = {left} {base_op} {right};")

    # Function to handle return statements
    def t_Return(self, node: c_ast.Return) -> None:
        out_chan = getattr(self, "_current_ret", "ret")
        self.w.write("{"); self.w.enter()
        value_expr = self._expr(node.expr) if node.expr else "0"
        ret_type = self.function_return_types.get(self._current_func, 'int')
        if ret_type != 'void':
            self.w.write(f"{out_chan} ! {value_expr};")
        self.w.write(f"goto {self._exit_label};")
        self.w.exit(); self.w.write("}")

    # Function to handle if statements
    def t_If(self, node: c_ast.If) -> None:
        cond = self._expr(node.cond)
        self.w.write("if"); self.w.enter()
        self.w.write(f":: {cond} ->"); self.w.enter(); self._visit(node.iftrue); self.w.exit()
        self.w.write(":: else ->"); self.w.enter()
        if node.iffalse:
            self._visit(node.iffalse)
        else:
            parent = self._parent_map.get(node)
            if isinstance(parent, c_ast.Compound):
                sibs = parent.block_items or []
                idx = sibs.index(node)
                if idx + 1 < len(sibs) and isinstance(sibs[idx + 1], c_ast.Return):
                    self._visit(sibs[idx + 1])
                    self._skip_set.add(sibs[idx + 1])
        self.w.exit(); self.w.exit(); self.w.write("fi")

    # Function to handle while loops
    def t_While(self, node: c_ast.While) -> None:
        is_infinite = isinstance(node.cond, c_ast.Constant) and node.cond.value in ("1", "true")
        cond = self._expr(node.cond)
        self.w.write("do"); self.w.enter()
        self.w.write(f":: {cond} ->"); self.w.enter(); self._visit(node.stmt); self.w.exit()
        if not is_infinite:
            self.w.write(":: else -> break;")
        self.w.exit(); self.w.write("od;")

    # Function to handle for loops
    def t_For(self, node: c_ast.For) -> None:
        if node.init:
            if isinstance(node.init, c_ast.Assignment) \
                and isinstance(node.init.lvalue, c_ast.ID) \
                and node.init.lvalue.name in self.initialized_vars:
                    pass
            else:
                self._visit(node.init)
        cond = self._expr(node.cond) if node.cond else 'true'
        self.w.write("do"); self.w.enter()
        self.w.write(f":: {cond} ->"); self.w.enter()
        self._visit(node.stmt)
        if node.next:
            if isinstance(node.next, c_ast.UnaryOp) and node.next.op == 'p++':
                var = node.next.expr.name; self.w.write(f"{var} = {var} + 1;")
            elif isinstance(node.next, c_ast.UnaryOp) and node.next.op == 'p--':
                var = node.next.expr.name; self.w.write(f"{var} = {var} - 1;")
            else:
                incr = self._expr(node.next); self.w.write(f"{incr};")
        self.w.exit(); self.w.write(":: else -> break;")
        self.w.exit(); self.w.write("od;")

    # Function to handle switch statements
    def t_Switch(self, node: c_ast.Switch) -> None:
        var = self._expr(node.cond)
        cases: List[tuple[str, List[c_ast.Node]]] = []
        default_body: Optional[List[c_ast.Node]] = None
        for stmt in node.stmt.block_items or []:
            if isinstance(stmt, c_ast.Case):
                val = self._expr(stmt.expr)
                cases.append((val, stmt.stmts or []))
            elif isinstance(stmt, c_ast.Default):
                default_body = stmt.stmts or []
        self.w.write("if"); self.w.enter()
        for val, stmts in cases:
            self.w.write(f":: ({var} == {val}) ->"); self.w.enter()
            for s in stmts: self._visit(s)
            self.w.exit()
        if default_body is not None:
            self.w.write(":: else ->"); self.w.enter()
            for s in default_body: self._visit(s)
            self.w.exit()
        self.w.exit(); self.w.write("fi")

    # Function to handle break statements
    def t_Break(self, node: c_ast.Break) -> None:
        self.w.write("break;")

    # Function to handle function calls
    def t_FuncCall(self, node: c_ast.FuncCall) -> Optional[str]:
        fname = node.name.name if isinstance(node.name, c_ast.ID) else "UNKNOWN"
        if fname in ('malloc', 'free'):
            return None
        actuals: List[str] = []
        if node.args:
            for e in node.args.exprs:
                actuals.append(self._expr(e))
        ret_type = self.function_return_types.get(fname, 'int')
        if ret_type == 'void':
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

    # Function to handle expressions
    def _expr(self, node: c_ast.Node) -> str:
        if isinstance(node, c_ast.ID) and node.name in self._static_map:
            return f"mem[{self._static_map[node.name]}]"
        if isinstance(node, c_ast.TernaryOp):
            return self.t_TernaryOp(node)
        if isinstance(node, c_ast.ID) and node.name in C_SPECIAL_CONST:
            return C_SPECIAL_CONST[node.name]
        if isinstance(node, c_ast.UnaryOp) and node.op == '&':
            tgt = node.expr
            if isinstance(tgt, c_ast.ID):
                return str(self._alloc_static(tgt.name))
            if isinstance(tgt, c_ast.ArrayRef):
                base = self._expr(tgt.name)
                idx = self._expr(tgt.subscript)
                return f"({base} + {idx})"
        if isinstance(node, c_ast.UnaryOp) and node.op == '*':
            ptr = self._expr(node.expr)
            return f"mem[{ptr}]"
        if isinstance(node, c_ast.UnaryOp) and node.op == 'sizeof':
            return self._sizeof_value(node)
        if isinstance(node, c_ast.BinaryOp) and node.op in ('+', '-', '+=', '-='):
            L = self._expr(node.left)
            R = self._expr(node.right)
            return f"({L} {node.op} {R})"
        if isinstance(node, c_ast.StructRef):
            fname = node.field.name
            if node.type == '->':
                off = self._field_offset(fname)
                base = self._expr(node.name)
                return f"mem[{base} + {off}]"
            base = self._expr(node.name)
            return f"{base}.{fname}"
        if isinstance(node, c_ast.ArrayRef):
            base = self._expr(node.name)
            idx = self._expr(node.subscript)
            if getattr(node.name, 'name', None) in self.var_types and self.var_types[node.name.name] == 'int':
                return f"mem[{base} + {idx}]"
            return f"{base}[{idx}]"
        if isinstance(node, c_ast.Cast):
            return self._expr(node.expr)
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
            if node.op in ('p++','++') and isinstance(node.expr, c_ast.ID) and \
               self.var_types.get(node.expr.name) == 'int':
                return f"{node.expr.name} = {node.expr.name} + {PTR_SIZE}"
            if node.op in ('p--','--') and isinstance(node.expr, c_ast.ID) and \
               self.var_types.get(node.expr.name) == 'int':
                return f"{node.expr.name} = {node.expr.name} - {PTR_SIZE}"
            inner = self._expr(node.expr)
            op = node.op
            if op == "p++":
                return f"({inner}++)"
            if op == "p--":
                return f"({inner}--)"
            return f"({op}{inner})" 
        if isinstance(node, c_ast.FuncCall):
            name_id = node.name.name if isinstance(node.name, c_ast.ID) else ""
            if name_id == 'malloc':
                size_s = self._expr(node.args.exprs[0])
                return self._emit_malloc(size_s)
            if name_id == 'free':
                ptr = self._expr(node.args.exprs[0])
                self.w.write(f"/* free({ptr}); */")
                return ""
            tmp = self.t_FuncCall(node)
            return tmp or ""
        if isinstance(node, c_ast.TernaryOp):
            return self.t_TernaryOp(node)
        
        
        raise NotImplementedError(f"Expr not supported: {type(node)}")

    # Generic handler for unsupported nodes
    def generic(self, node: c_ast.Node, *args: Any, **kw: Any) -> None:
        raise NotImplementedError(f"No handler for {type(node)}")