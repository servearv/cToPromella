#include <stdbool.h>

int test_ops(int a, int b, char c, int arr[2]) {
    // 1) Prefix/Postfix ++ and --  
    int ppre  = ++a;     // prefix increment  
    int ppost = b--;     // postfix decrement  

    // 2) Ternary  
    int tval  = (ppre > ppost ? ppre : ppost);

    // 3) Logical && and ||  
    bool land = (ppre > 0) && (ppost < 0);
    bool lor  = (ppre == 0) || (ppost == 0);

    // 4) Bitwise ^ (XOR) and ~ (NOT)  
    int bxor = ppre ^ ppost;
    int bnot = ~bxor;

    // 5) Compound assignments  
    ppre   += 10;
    ppost  -=  5;
    bxor   ^=  0xF;
    int band = bxor & ppost;
    int bor  = bxor | ppost;
    arr[0] <<= 1;
    arr[1] >>= 1;

    // 6) sizeof  
    int len = sizeof(arr) / sizeof(arr[0]);

    // 7) Mix them all in a return expression
    return ppre + ppost + tval + land + lor + bxor + bnot + band + bor + len;
}

int main() {
    int a   = 1, b = 2;
    char c  = 'X';
    int arr[2] = { 3, 4 };

    int res = test_ops(a, b, c, arr);
    // final ternary for exit code:
    return (res > 100 ? 1 : 0);
}
