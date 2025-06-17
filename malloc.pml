byte mem[1024];
int heap_next = 0;
typedef node {
    int next;
    int value;
}
proctype test() {
    int tmp_malloc_1;
    atomic {
        tmp_malloc_1 = heap_next;
        heap_next = heap_next + 1;
    }
    int p = tmp_malloc_1;
    mem[p + 1] = 99;
    end_test: skip;
}
init {
    run test()
}
