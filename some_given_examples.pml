byte mem[1024];
int heap_next = 0;
typedef MyStruct {
    int a;
    byte b;
    int c;
}
int a[10];
proctype f_struct(chan ret = [0] of { MyStruct }) {
    MyStruct s;
    {
        ret ! s;
        goto end_f_struct;
    }
    end_f_struct: skip;
}
proctype gcd(chan ret = [0] of { int }; int x; int y) {
    if
        :: (y == 0) ->
            {
                ret ! x;
                goto end_gcd;
            }
        :: else ->
            {
                chan ret_gcd_1 = [0] of { int };
                int tmp_gcd_2;
                run gcd(ret_gcd_1, y, (x % y));
                ret_gcd_1 ? tmp_gcd_2;
                ret ! tmp_gcd_2;
                goto end_gcd;
            }
    fi
    end_gcd: skip;
}
proctype test(chan ret = [0] of { int }; int a; int b) {
    if
        :: (a >= b) ->
            {
                ret ! a;
                goto end_test;
            }
        :: else ->
            {
                ret ! b;
                goto end_test;
            }
    fi
    end_test: skip;
}
int b = 0;
mem[0] = b;
int c = 0;
mem[1] = c;
int d;
mem[2] = d;
proctype main(chan ret = [0] of { int }) {
    int tmp_ternary_3;
    if
        :: (mem[0] > mem[1]) -> tmp_ternary_3 = mem[0];
        :: else -> tmp_ternary_3 = mem[1];
    fi;
    mem[2] = tmp_ternary_3;
    do
        :: 1 ->
            if
                :: (mem[a + 0] > mem[0]) ->
                    break;
                :: else ->
                    mem[a + 0] = mem[a + 0] + 1;
            fi
    od;
    int x = 0;
    if
        :: (x == 0) ->
            mem[0] = mem[0] + 1;
            mem[0] = mem[0] + 1;
        :: (x == 1) ->
            mem[0] = mem[0] - 1;
            mem[0] = mem[0] - 1;
        :: else ->
            break;
    fi
    int i = 1;
    int n = 10;
    do
        :: (i < n) ->
            x = (x + i);
            i = i + 1;
        :: else -> break;
    od;
    int i = 1;
    do
        :: 1 ->
            if
                :: (i > n) ->
                    break;
                :: else ->
            fi
            i = i + 1;
    od;
    int x = 2;
    int y = 3;
    chan ret_test_4 = [0] of { int };
    int tmp_test_5;
    run test(ret_test_4, x, y);
    ret_test_4 ? tmp_test_5;
    {
        ret ! 0;
        goto end_main;
    }
    end_main: skip;
}
init {
    chan ret_entry = [0] of { int };
    run main(ret_entry)
    ret_entry ? 0;
}
