int main() {
    int i, j;
    int total = 0;
    for (i = 0; i < 3; i++) {
        for (j = 0; j < 2; j++) {
            total = total + (i * j);
        }
    }
    return total;
}
