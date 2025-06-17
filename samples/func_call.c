void test(int a, int b) {
    if(a>=b) b=++a;
    else b++;
}
int main() {
    int x=2;
    int y=3;
    test(x, y);
    return 0;
}