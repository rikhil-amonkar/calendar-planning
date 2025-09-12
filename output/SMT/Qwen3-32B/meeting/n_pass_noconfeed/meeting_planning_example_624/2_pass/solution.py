def build_travel_time_expr(loc_prev, loc_curr):
    curr_expr_1 = If(loc_curr == 1, 0, 
                     If(loc_curr == 2, 23, 
                     If(loc_curr == 3, 6, 
                     If(loc_curr == 4, 19, 
                     If(loc_curr == 5, 5, 
                     If(loc_curr == 6, 19, 
                     If(loc_curr == 7, 17, 0)))))))

    curr_expr_2 = If(loc_curr == 1, 22, 
                     If(loc_curr == 2, 0, 
                     If(loc_curr == 3, 24, 
                     If(loc_curr == 4, 12, 
                     If(loc_curr == 5, 20, 
                     If(loc_curr == 6, 6, 
                     If(loc_curr == 7, 7, 0)))))))

    curr_expr_3 = If(loc_curr == 1, 6, 
                     If(loc_curr == 2, 24, 
                     If(loc_curr == 3, 0, 
                     If(loc_curr == 4, 20, 
                     If(loc_curr == 5, 8, 
                     If(loc_curr == 6, 20, 
                     If(loc_curr == 7, 18, 0)))))))

    curr_expr_4 = If(loc_curr == 1, 19, 
                     If(loc_curr == 2, 8, 
                     If(loc_curr == 3, 22, 
                     If(loc_curr == 4, 0, 
                     If(loc_curr == 5, 17, 
                     If(loc_curr == 6, 3, 
                     If(loc_curr == 7, 7, 0)))))))

    curr_expr_5 = If(loc_curr == 1, 5, 
                     If(loc_curr == 2, 19, 
                     If(loc_curr == 3, 8, 
                     If(loc_curr == 4, 16, 
                     If(loc_curr == 5, 0, 
                     If(loc_curr == 6, 15, 
                     If(loc_curr == 7, 13, 0)))))))

    curr_expr_6 = If(loc_curr == 1, 18, 
                     If(loc_curr == 2, 6, 
                     If(loc_curr == 3, 22, 
                     If(loc_curr == 4, 16, 
                     If(loc_curr == 5, 0, 
                     If(loc_curr == 6, 4, 
                     If(loc_curr == 7, 5, 0)))))))

    curr_expr_7 = If(loc_curr == 1, 17, 
                     If(loc_curr == 2, 7, 
                     If(loc_curr == 3, 21, 
                     If(loc_curr == 4, 9, 
                     If(loc_curr == 5, 15, 
                     If(loc_curr == 6, 5, 
                     If(loc_curr == 7, 0, 0)))))))

    expr = If(loc_prev == 1, curr_expr_1,
              If(loc_prev == 2, curr_expr_2,
              If(loc_prev == 3, curr_expr_3,
              If(loc_prev == 4, curr_expr_4,
              If(loc_prev == 5, curr_expr_5,
              If(loc_prev == 6, curr_expr_6,
              If(loc_prev == 7, curr_expr_7, 0)))))))
    return expr