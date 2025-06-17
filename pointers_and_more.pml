byte mem[1024];
int heap_next = 0;
typedef MyStruct {
    int a;
    byte b;
    bool c;
}
proctype f_int(chan ret = [0] of { int }) {
    {
        ret ! (-42);
        goto end_f_int;
    }
    end_f_int: skip;
}
proctype f_uint(chan ret = [0] of { int }) {
    {
        ret ! 42;
        goto end_f_uint;
    }
    end_f_uint: skip;
}
proctype f_short(chan ret = [0] of { int }) {
    {
        ret ! 123;
        goto end_f_short;
    }
    end_f_short: skip;
}
proctype f_long(chan ret = [0] of { int }) {
    {
        ret ! 1000000;
        goto end_f_long;
    }
    end_f_long: skip;
}
proctype f_char(chan ret = [0] of { byte }) {
    {
        ret ! 'Z';
        goto end_f_char;
    }
    end_f_char: skip;
}
proctype f_bool(chan ret = [0] of { bool }) {
    {
        ret ! true;
        goto end_f_bool;
    }
    end_f_bool: skip;
}
proctype f_float(chan ret = [0] of { int }) {
    {
        ret ! 3;
        goto end_f_float;
    }
    end_f_float: skip;
}
proctype f_double(chan ret = [0] of { int }) {
    {
        ret ! 2;
        goto end_f_double;
    }
    end_f_double: skip;
}
proctype f_void() {
    end_f_void: skip;
}
int g_storage = 7;
mem[0] = g_storage;
proctype f_ptr(chan ret = [0] of { int }) {
    {
        ret ! 0;
        goto end_f_ptr;
    }
    end_f_ptr: skip;
}
proctype f_nullptr(chan ret = [0] of { int }) {
    {
        ret ! 0;
        goto end_f_nullptr;
    }
    end_f_nullptr: skip;
}
proctype f_struct(chan ret = [0] of { MyStruct }) {
    MyStruct s;
    {
        ret ! s;
        goto end_f_struct;
    }
    end_f_struct: skip;
}
proctype mix_params(chan ret = [0] of { bool }; int x; int u; int s; int l; byte ch; bool flag; int fl; int d; int p; MyStruct m) {
    {
        ret ! ((((((((((x < 0) || (u > 0)) || (s == 123)) || (l == 1000000)) || (ch == 'X')) || (!flag)) || (fl > 0)) || (d > 2)) || (mem[p] == 7)) || (m.b == 'X'));
        goto end_mix_params;
    }
    end_mix_params: skip;
}
proctype main(chan ret = [0] of { int }) {
    chan ret_f_int_1 = [0] of { int };
    int tmp_f_int_2;
    run f_int(ret_f_int_1);
    ret_f_int_1 ? tmp_f_int_2;
    int i = tmp_f_int_2;
    chan ret_f_uint_3 = [0] of { int };
    int tmp_f_uint_4;
    run f_uint(ret_f_uint_3);
    ret_f_uint_3 ? tmp_f_uint_4;
    int ui = tmp_f_uint_4;
    chan ret_f_short_5 = [0] of { int };
    int tmp_f_short_6;
    run f_short(ret_f_short_5);
    ret_f_short_5 ? tmp_f_short_6;
    int ss = tmp_f_short_6;
    chan ret_f_long_7 = [0] of { int };
    int tmp_f_long_8;
    run f_long(ret_f_long_7);
    ret_f_long_7 ? tmp_f_long_8;
    int ll = tmp_f_long_8;
    chan ret_f_char_9 = [0] of { byte };
    byte tmp_f_char_10;
    run f_char(ret_f_char_9);
    ret_f_char_9 ? tmp_f_char_10;
    byte cc = tmp_f_char_10;
    chan ret_f_bool_11 = [0] of { bool };
    bool tmp_f_bool_12;
    run f_bool(ret_f_bool_11);
    ret_f_bool_11 ? tmp_f_bool_12;
    bool bb = tmp_f_bool_12;
    chan ret_f_float_13 = [0] of { int };
    int tmp_f_float_14;
    run f_float(ret_f_float_13);
    ret_f_float_13 ? tmp_f_float_14;
    int ff = tmp_f_float_14;
    chan ret_f_double_15 = [0] of { int };
    int tmp_f_double_16;
    run f_double(ret_f_double_15);
    ret_f_double_15 ? tmp_f_double_16;
    int dd = tmp_f_double_16;
    run f_void();
    chan ret_f_ptr_17 = [0] of { int };
    int tmp_f_ptr_18;
    run f_ptr(ret_f_ptr_17);
    ret_f_ptr_17 ? tmp_f_ptr_18;
    int ptr1 = tmp_f_ptr_18;
    chan ret_f_nullptr_19 = [0] of { int };
    int tmp_f_nullptr_20;
    run f_nullptr(ret_f_nullptr_19);
    ret_f_nullptr_19 ? tmp_f_nullptr_20;
    int ptr2 = tmp_f_nullptr_20;
    int val1 = mem[ptr1];
    int tmp_ternary_21;
    if
        :: (ptr2 == 0) -> tmp_ternary_21 = 0;
        :: else -> tmp_ternary_21 = mem[ptr2];
    fi;
    int val2 = tmp_ternary_21;
    MyStruct ms;
    chan ret_mix_params_22 = [0] of { bool };
    bool tmp_mix_params_23;
    run mix_params(ret_mix_params_22, i, ui, ss, ll, cc, bb, ff, dd, ptr1, ms);
    ret_mix_params_22 ? tmp_mix_params_23;
    bool ok = tmp_mix_params_23;
    {
        int tmp_ternary_24;
        if
            :: ok -> tmp_ternary_24 = 1;
            :: else -> tmp_ternary_24 = 0;
        fi;
        ret ! tmp_ternary_24;
        goto end_main;
    }
    end_main: skip;
}
init {
    chan ret_entry = [0] of { int };
    run main(ret_entry)
    ret_entry ? 0;
}
