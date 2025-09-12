for friend in friends_data:
    available_start = friends_data[friend].get('available_start', 0)
    print(f"{friend}'s available start time: {available_start}")