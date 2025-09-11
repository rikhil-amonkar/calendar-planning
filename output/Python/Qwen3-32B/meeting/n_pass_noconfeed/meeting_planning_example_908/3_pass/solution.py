# Define the arrival time and friend's start time
arrival_time = 15  # Example value in hours (3 PM)
friend_start = 14  # Example value in hours (2 PM)

# Compute the possible start time
possible_start = max(arrival_time, friend_start)

# Output the result
print(f"Possible start time is at {possible_start}:00")