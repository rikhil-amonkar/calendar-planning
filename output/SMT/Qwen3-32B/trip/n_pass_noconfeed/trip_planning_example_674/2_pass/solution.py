last_day = S[5] + z3.If(order[5] == 0, 2,
                           z3.If(order[5] == 1, 3,
                                 z3.If(order[5] == 2, 4,
                                       z3.If(order[5] == 3, 4,
                                             z3.If(order[5] == 4, 2,
                                                   z3.If(order[5] == 5, 4, 0)))))) - 1