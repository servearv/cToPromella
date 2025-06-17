/*
 * translator_test_types.c
 * Exercise every C→Promela type mapping and return type supported:
 *  - int, unsigned, short, long
 *  - char (mapped to byte)
 *  - float, double (mapped to int)
 *  - bool (mapped to bool)
 *  - void functions
 *  - pointer return (int*) and address-of/dereference
 *  - struct user-defined types
 */

#include <stdbool.h>
#include <stddef.h>

// 1) Primitive-return functions
int    f_int(void)       { return -42; }
unsigned f_uint(void)    { return  42u; }
short  f_short(void)     { return  (short)123; }
long   f_long(void)      { return  1000000L; }
char   f_char(void)      { return 'Z'; }
bool   f_bool(void)      { return true; }
float  f_float(void)     { return 3.14f; }
double f_double(void)    { return 2.71828; }

// 2) Void-return
void   f_void(void)      { /* no return */ }

// 3) Pointer return and NULL
int  g_storage = 7;
int* f_ptr(void)        { return &g_storage; }
int* f_nullptr(void)    { return NULL; }

// 4) Struct type and typedef
typedef struct {
    int  a;
    char b;
    bool c;
} MyStruct;

MyStruct f_struct(void) {
    MyStruct s = { .a = 10, .b = 'X', .c = false };
    return s;
}

// 5) Mixed-parameter function
bool mix_params(int x, unsigned u, short s, long l,
                char ch, bool flag, float fl, double d,
                int* p, MyStruct m) {
    // simple checks
    return (x < 0)
        || (u > 0)
        || (s == (short)123)
        || (l == 1000000L)
        || (ch == 'X')
        || !flag
        || (fl > 0)
        || (d > 2.0)
        || (*p == 7)
        || (m.b == 'X');
}

// 6) main invokes all
int main(void) {
    int       i  = f_int();
    unsigned  ui = f_uint();
    short     ss = f_short();
    long      ll = f_long();
    char      cc = f_char();
    bool      bb = f_bool();
    float     ff = f_float();
    double    dd = f_double();

    f_void();

    int* ptr1 = f_ptr();
    int* ptr2 = f_nullptr();
    int  val1 = *ptr1;
    int  val2 = (ptr2 == NULL) ? 0 : *ptr2;

    MyStruct ms = f_struct();
    bool    ok = mix_params(i, ui, ss, ll, cc, bb, ff, dd, ptr1, ms);

    return ok ? 1 : 0;
}
