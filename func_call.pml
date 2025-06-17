proctype test(int a; int b) {
    if
        :: (a >= b) ->
            b = (++a);
        :: else ->
            b = b + 1;
    fi
    end_test: skip;
}
proctype main(chan ret = [0] of { int }) {
    int x = 2;
    int y = 3;
    run test(x, y);
    {
        ret ! 0;
        goto end_main;
    }
    end_main: skip;
}
init {
    run main(chan ret_entry = [0] of { int })
    ret_entry ? 0;
}
