travel_time_expr = If(current_loc == 1, 19,
                      If(current_loc == 2, 16,
                         If(current_loc == 3, 8,
                            If(current_loc == 4, 24,
                               If(current_loc == 5, 11, 0)))))  # <<--- Added 3 closing parentheses