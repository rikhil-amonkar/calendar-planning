# Define available_start, available_end, duration, and loc for friend_i
available_start_expr = If(friend_i == 0, 420,
    If(friend_i == 1, 570,
        If(friend_i == 2, 735,
            If(friend_i == 3, 735,
                If(friend_i == 4, 450,
                    If(friend_i == 5, 705,
                        If(friend_i == 6, 750,
                            If(friend_i == 7, 1170, 0)))))))))  # +1 added closing parenthesis

available_end_expr = If(friend_i == 0, 1005,
    If(friend_i == 1, 1035,
        If(friend_i == 2, 1140,
            If(friend_i == 3, 1080,
                If(friend_i == 4, 1200,
                    If(friend_i == 5, 810,
                        If(friend_i == 6, 885,
                            If(friend_i == 7, 1290, 0)))))))))  # +1 added closing parenthesis

duration_expr = If(friend_i == 0, 105,
    If(friend_i == 1, 105,
        If(friend_i == 2, 90,
            If(friend_i == 3, 45,
                If(friend_i == 4, 90,
                    If(friend_i == 5, 75,
                        If(friend_i == 6, 90,
                            If(friend_i == 7, 120, 0)))))))))  # +1 added closing parenthesis

loc_expr = If(friend_i == 0, 1,
    If(friend_i == 1, 2,
        If(friend_i == 2, 3,
            If(friend_i == 3, 4,
                If(friend_i == 4, 5,
                    If(friend_i == 5, 6,
                        If(friend_i == 6, 7,
                            If(friend_i == 7, 8, 0)))))))))  # +1 added closing parenthesis