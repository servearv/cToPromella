int sum_array() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = 0;
    int i;

    for (i = 0; i < 5; i++) {
        sum = sum + arr[i];
    }

    return sum;
}
