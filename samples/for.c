int main() {
    int i;
    int sum1 = 0;
    int sum2 = 0;
    // post-increment
    for (i = 0; i < 4; i++) {
        sum1 = sum1 + i;
    }
    // post-decrement
    for (i = 4; i > 0; i--) {
        sum2 = sum2 + i;
    }
    return sum1 + sum2;
}
