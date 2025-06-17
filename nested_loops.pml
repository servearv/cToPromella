inline main(__ret_main) {
    int i;
    int j;
    int total = 0;
    i = 0;
    do
        :: (i < 3) ->
            j = 0;
            do
                :: (j < 2) ->
                    total = (total + (i * j));
                    j = j + 1;
                :: else -> break;
            od;
            i = i + 1;
        :: else -> break;
    od;
    __ret_main = total;
}
init {
    int __retval;
    main(__retval);
}
