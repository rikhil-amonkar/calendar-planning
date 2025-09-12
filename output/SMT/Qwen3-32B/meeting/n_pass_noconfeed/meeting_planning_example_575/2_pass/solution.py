return If(friend_idx_var == 0, friends[0]['end'],
          If(friend_idx_var == 1, friends[1]['end',
             If(friend_idx_var == 2, friends[2]['end',
                If(friend_idx_var == 3, friends[3]['end',
                   If(friend_idx_var == 4, friends[4]['end',
                      friends[5]['end'])))))))  # 5 closing parentheses