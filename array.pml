proctype sum_array(chan ret = [0] of { int }) {
    int arr[5];
    arr[0] = 1;
    arr[1] = 2;
    arr[2] = 3;
    arr[3] = 4;
    arr[4] = 5;
    int sum = 0;
    int i;
    i = 0;
    do
        :: (i < 5) ->
            sum = (sum + arr[i]);
            i = i + 1;
        :: else -> break;
    od;
    {
        ret ! sum;
        goto end_sum_array;
    }
    end_sum_array: skip;
}
init {
    run sum_array(chan ret_entry = [0] of { int })
    ret_entry ? 0;
}
