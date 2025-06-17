int main() {
    int count = 0;
    int n = 5;
    while (n > 0) {
        if (n == 2) {
            break;
        }
        count = count + n;
        n--;
    }
    return count;
}