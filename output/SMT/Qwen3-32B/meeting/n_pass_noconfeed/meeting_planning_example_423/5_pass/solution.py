# Define sample friends data
friends_data = {
    'Alice': {'available_start': 9},
    'Bob': {'available_start': 10},
    'Charlie': {'available_start': 8, 'other_key': 'value'}
}

# Loop through the friends data
for friend in friends_data:
    available_start = friends_data[friend].get('available_start', 0)
    print(f"{friend}'s available start time: {available_start}")