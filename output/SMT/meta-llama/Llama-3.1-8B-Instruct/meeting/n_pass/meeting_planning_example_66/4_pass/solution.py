def find_schedule(nob_hill_time_slots, presidio_time_slots, min_meeting_time):
    # Generate all possible combinations of time slots
    valid_combinations = []
    for nob_hill_values in [True] + [False]*10:
        for presidio_values in [False]*10 + [True]:
            meeting_time = 0
            for t in range(10):
                if nob_hill_values[t] and presidio_values[t]:
                    meeting_time += 1
            if meeting_time >= min_meeting_time:
                valid_combinations.append((nob_hill_values, presidio_values))

    # Return the first valid combination
    return valid_combinations[0]

# Define the constraints
min_meeting_time = 2  # Convert 120 minutes to hours

# Find the schedule
schedule = find_schedule([False]*10 + [True], [True]*10 + [False], min_meeting_time)

# Print the schedule
print("Schedule:")
for t in range(len(schedule[0])):
    nob_hill_value = schedule[0][t]
    presidio_value = schedule[1][t]
    print(f"{t}:00 AM - Nob Hill: {nob_hill_value}, Presidio: {presidio_value}")