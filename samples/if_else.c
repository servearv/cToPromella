int main() {
    int x = 4;
    int y = 9;
    if (x < y) {
        x = x * 2;
    } else {
        x = x + 5;
    }
    // nested
    if (x % 3 == 0) {
        y = y - 1;
    } else {
        y = y + 1;
    }
    return x + y;
}
