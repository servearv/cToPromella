inline main(__ret_main) {
    int code = 3;
    int out = 0;
    if
        :: (code == 1) ->
            out = 10;
        :: (code == 2) ->
            out = 20;
        :: (code == 3) ->
            out = 30;
        :: else ->
            out = 99;
    fi
    __ret_main = out;
}
init {
    int __retval;
    main(__retval);
}
