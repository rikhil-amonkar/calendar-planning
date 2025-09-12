else:
    prev_friend = friends_order[i - 1]
    current_friend = friends_order[i]
    travel_time = (
        (0 if current_friend == 0 else
         19 if current_friend == 1 else
         10 if current_friend == 2 else 17) if prev_friend == 0 else
        (21 if current_friend == 0 else
         0 if current_friend == 1 else
         15 if current_friend == 2 else 16) if prev_friend == 1 else
        (9 if current_friend == 0 else
         13 if current_friend == 1 else
         0 if current_friend == 2 else 10) if prev_friend == 2 else
        (17 if current_friend == 0 else
         15 if current_friend == 1 else
         11 if current_friend == 2 else 0)
    )