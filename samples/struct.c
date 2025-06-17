

// Named struct with typedef alias
struct Vector {
    float x;
    float y;
};
typedef struct Vector Vec2;

// Anonymous struct with typedef
typedef struct {
    double real;
    double imag;
} Complex;

// Struct with pointer and array fields
typedef struct Matrix {
    float data;
    int rows;
    int cols;
    double weights;
} Matrix;

// Typedef to forward-declared struct (should be recorded as empty if struct not defined)
typedef struct Forward ForwardAlias;

struct node {
    int value;
};
struct node n[10];

