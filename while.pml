byte mem[1024];
int heap_next = 0;
proctype main(chan ret = [0] of { int }) {
    int count = 0;
    int n = 5;
    do
        :: (n > 0) ->
            if
                :: (n == 2) ->
                    break;
                :: else ->
            fi
            count = (count + n);
            n = n - 1;
        :: else -> break;
    od;
    {
        ret ! count;
        goto endmain;
    }
    endmain: skip;
}
init {
    chan ret_entry = [0] of { int };
    run main(ret_entry)
    ret_entry ? 0;
}
