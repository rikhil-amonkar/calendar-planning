def get_travel_time_expr(prev_p, curr_p):
    return If(
        prev_p == 0,
        If(curr_p == 0, people_travel_time[0][0],
           If(curr_p == 1, people_travel_time[0][1],
              If(curr_p == 2, people_travel_time[0][2],
                 If(curr_p == 3, people_travel_time[0][3], 0)))),
        If(prev_p == 1,
           If(curr_p == 0, people_travel_time[1][0],
              If(curr_p == 1, people_travel_time[1][1],
                 If(curr_p == 2, people_travel_time[1][2],
                    If(curr_p == 3, people_travel_time[1][3], 0)))),
           If(prev_p == 2,
              If(curr_p == 0, people_travel_time[2][0],
                 If(curr_p == 1, people_travel_time[2][1],
                    If(curr_p == 2, people_travel_time[2][2],
                       If(curr_p == 3, people_travel_time[2][3], 0)))),
              If(prev_p == 3,
                 If(curr_p == 0, people_travel_time[3][0],
                    If(curr_p == 1, people_travel_time[3][1],
                       If(curr_p == 2, people_travel_time[3][2],
                          If(curr_p == 3, people_travel_time[3][3], 0)))),
                 0)))
    )