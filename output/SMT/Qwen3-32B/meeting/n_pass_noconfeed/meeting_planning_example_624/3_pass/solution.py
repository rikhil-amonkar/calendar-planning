def build_travel_time_expr(loc_prev, loc_curr):
    curr_expr_1 = 0 if loc_curr == 1 else (23 if loc_curr == 2 else (6 if loc_curr == 3 else (19 if loc_curr == 4 else (5 if loc_curr == 5 else (19 if loc_curr == 6 else (17 if loc_curr == 7 else 0)))))))

    curr_expr_2 = 22 if loc_curr == 1 else (0 if loc_curr == 2 else (24 if loc_curr == 3 else (12 if loc_curr == 4 else (20 if loc_curr == 5 else (6 if loc_curr == 6 else (7 if loc_curr == 7 else 0)))))))

    curr_expr_3 = 6 if loc_curr == 1 else (24 if loc_curr == 2 else (0 if loc_curr == 3 else (20 if loc_curr == 4 else (8 if loc_curr == 5 else (20 if loc_curr == 6 else (18 if loc_curr == 7 else 0)))))))

    curr_expr_4 = 19 if loc_curr == 1 else (12 if loc_curr == 2 else (22 if loc_curr == 3 else (0 if loc_curr == 4 else (17 if loc_curr == 5 else (3 if loc_curr == 6 else (7 if loc_curr == 7 else 0)))))))

    curr_expr_5 = 5 if loc_curr == 1 else (19 if loc_curr == 2 else (8 if loc_curr == 3 else (16 if loc_curr == 4 else (0 if loc_curr == 5 else (15 if loc_curr == 6 else (13 if loc_curr == 7 else 0)))))))

    curr_expr_6 = 18 if loc_curr == 1 else (6 if loc_curr == 2 else (22 if loc_curr == 3 else (16 if loc_curr == 4 else (15 if loc_curr == 5 else (4 if loc_curr == 6 else (5 if loc_curr == 7 else 0)))))))

    curr_expr_7 = 17 if loc_curr == 1 else (7 if loc_curr == 2 else (21 if loc_curr == 3 else (9 if loc_curr == 4 else (15 if loc_curr == 5 else (5 if loc_curr == 6 else (0 if loc_curr == 7 else 0)))))))

    expr = curr_expr_1 if loc_prev == 1 else (curr_expr_2 if loc_prev == 2 else (curr_expr_3 if loc_prev == 3 else (curr_expr_4 if loc_prev == 4 else (curr_expr_5 if loc_prev == 5 else (curr_expr_6 if loc_prev == 6 else (curr_expr_7 if loc_prev == 7 else 0)))))))
    return expr