int a[10];

// 4) Struct type and typedef
typedef struct {
    int  a;
    char b;
    int c;
} MyStruct;

MyStruct f_struct(void) {
    MyStruct s = { .a = 10, .b = 'X', .c = 0 };
    return s;
}

int gcd(int x, int y){
    if(y==0) return x;
    else return gcd(y, x%y);
}

int test(int a, int b){
    if(a>=b) return a;
    else return b;
}

int b=0,c=0, d;

int main() {
    d = ( b>c ) ? b : c;

    while(1){
        if (a[0]>b) break;
        else a[0]++;
    }

    int x = 0;
    switch(x){
        case 0:
            b++;
            b++;
        case 1:
            b--;
            b--;
        default:
            break;
    }

    int i=1;
    int n=10;
    for(; i<n; i++){
        x=x+i;
    }

    int i=1;
    while(1){
        if(i>n) break;
        i++;
    }

    int x = 2;
    int y = 3;
    test(x, y);

    return 0;
}
