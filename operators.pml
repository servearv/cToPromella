proctype test_ops(chan ret = [0] of { int }; int a; int b; byte c; int arr[2]) {
    a = a + 1;
    int ppre = a;
    int ppost = b;
    b = b - 1;
    int tmp_ternary_1;
    if
        :: (ppre > ppost) -> tmp_ternary_1 = ppre;
        :: else -> tmp_ternary_1 = ppost;
    fi;
    int tval = tmp_ternary_1;
    int land = ((ppre > 0) && (ppost < 0));
    int lor = ((ppre == 0) || (ppost == 0));
    int bxor = (ppre ^ ppost);
    int bnot = (~bxor);
    ppre = ppre + 10;
    ppost = ppost - 5;
    bxor = bxor ^ 0xF;
    int band = (bxor & ppost);
    int bor = (bxor | ppost);
    arr[0] = arr[0] << 1;
    arr[1] = arr[1] >> 1;
    int len = (1 / 4);
    {
        ret ! (((((((((ppre + ppost) + tval) + land) + lor) + bxor) + bnot) + band) + bor) + len);
        goto end_test_ops;
    }
    end_test_ops: skip;
}
proctype main(chan ret = [0] of { int }) {
    int a = 1;
    int b = 2;
    byte c = 'X';
    int arr[2];
    arr[0] = 3;
    arr[1] = 4;
    chan ret_test_ops_2 = [0] of { int };
    int tmp_test_ops_3;
    run test_ops(ret_test_ops_2, a, b, c, arr);
    ret_test_ops_2 ? tmp_test_ops_3;
    int res = tmp_test_ops_3;
    {
        int tmp_ternary_4;
        if
            :: (res > 100) -> tmp_ternary_4 = 1;
            :: else -> tmp_ternary_4 = 0;
        fi;
        ret ! tmp_ternary_4;
        goto end_main;
    }
    end_main: skip;
}
init {
    run main(chan ret_entry = [0] of { int })
    ret_entry ? 0;
}
