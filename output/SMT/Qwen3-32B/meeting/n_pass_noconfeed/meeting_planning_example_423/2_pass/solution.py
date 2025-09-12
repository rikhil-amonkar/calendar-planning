available_start_expr_1 = If(friend == 1, friends_data[1]['available_start'],
                            If(friend == 2, friends_data[2]['available_start'],
                               If(friend == 3, friends_data[3]['available_start'],
                                  If(friend == 4, friends_data[4]['available_start'],
                                     If(friend == 5, friends_data[5]['available_start'], 0))))