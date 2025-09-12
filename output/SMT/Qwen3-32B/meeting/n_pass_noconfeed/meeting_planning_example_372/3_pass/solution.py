if i > 0:
    # Previous code (if any) for when i > 0
    pass  # Replace with actual logic if needed
else:
    prev_friend = friends_order[i - 1]
    current_friend = friends_order[i]
    travel_time = (
        if(prev_friend == 0,
           if(current_friend == 0, 0,
              if(current_friend == 1, 19,
                 if(current_friend == 2, 10, 17))),
           if(prev_friend == 1,
              if(current_friend == 0, 21,
                 if(current_friend == 1, 0,
                    if(current_friend == 2, 15, 16))),
              if(prev_friend == 2,
                 if(current_friend == 0, 9,
                    if(current_friend == 1, 13,
                       if(current_friend == 2, 0, 10))),
                 if(current_friend == 0, 17,
                    if(current_friend == 1, 15,
                       if(current_friend == 2, 11, 0))))))
    )