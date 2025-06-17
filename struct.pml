byte mem[1024];
typedef Vec2 {
    float x;
    float y;
}
typedef Complex {
    double real;
    double imag;
}
typedef Matrix {
    float data;
    int rows;
    int cols;
    double weights;
}
typedef ForwardAlias {
}
typedef Vector {
    float x;
    float y;
}
typedef node {
    int value;
}
int None;
int None;
int n[10];
init {
    run main(chan ret_entry = [0] of { int })
    ret_entry ? 0;
}
