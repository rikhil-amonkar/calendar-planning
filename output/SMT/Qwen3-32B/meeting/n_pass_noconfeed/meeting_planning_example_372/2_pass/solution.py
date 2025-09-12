else:
        prev_friend = friends_order[i-1]
        current_friend = friends_order[i]
        travel_time = If(prev_friend == 0,
                         If(current_friend == 0, 0,
                            If(current_friend == 1, 19,
                               If(current_friend == 2, 10, 17))),
                         If(prev_friend == 1,
                            If(current_friend == 0, 21,
                               If(current_friend == 1, 0,
                                  If(current_friend == 2, 15, 16))),
                            If(prev_friend == 2,
                               If(current_friend == 0, 9,
                                  If(current_friend == 1, 13,
                                     If(current_friend == 2, 0, 10))),
                               If(current_friend == 0, 17,
                                  If(current_friend == 1, 15,
                                     If(current_friend == 2, 11, 0))))))  # ← One extra closing parenthesis added