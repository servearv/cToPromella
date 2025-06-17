int main() {
    int code = 3;
    int out = 0;
    switch (code) {
        case 1:
            out = 10;
            break;
        case 2:
            out = 20;
            break;
        case 3:
            out = 30;
            break;
        default:
            out = 99;
    }
    return out;
}
