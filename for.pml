inline main(__ret_main) {
    int i;
    int sum1 = 0;
    int sum2 = 0;
    i = 0;
    do
        :: (i < 4) ->
            sum1 = (sum1 + i);
            i = i + 1;
        :: else -> break;
    od;
    i = 4;
    do
        :: (i > 0) ->
            sum2 = (sum2 + i);
            i = i - 1;
        :: else -> break;
    od;
    __ret_main = (sum1 + sum2);
}
init {
    int __retval;
    main(__retval);
}
