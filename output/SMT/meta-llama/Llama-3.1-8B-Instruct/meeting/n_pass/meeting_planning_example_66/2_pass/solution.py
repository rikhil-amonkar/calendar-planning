from itertools import product

def find_schedule(nob_hill_time_slots, presidio_time_slots, min_meeting_time):
    # Generate all possible combinations of time slots
    combinations = list(product(*[nob_hill_time_slots, presidio_time_slots]))
    valid_combinations = []

    # Check each combination
    for combination in combinations:
        nob_hill_values, presidio_values = combination
        meeting_time = 0
        for t in range(len(nob_hill_time_slots)):
            if nob_hill_values[t] and presidio_values[t]:
                meeting_time += 1
        if meeting_time >= min_meeting_time:
            valid_combinations.append(combination)

    # Return the first valid combination
    return valid_combinations[0]

# Define the time slots
time_slots = [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

# Define the variables
nob_hill = [True, False, False, False, False, False, False, False, False, False, False, False]
presidio = [False, False, True, True, True, True, True, True, True, True, True, True]

# Define the constraints
min_meeting_time = 2  # Convert 120 minutes to hours

# Find the schedule
schedule = find_schedule(nob_hill, presidio, min_meeting_time)

# Print the schedule
print("Schedule:")
for t in range(len(nob_hill)):
    nob_hill_value = schedule[t]
    presidio_value = schedule[t + len(nob_hill)]
    print(f"{t}:00 AM - Nob Hill: {nob_hill_value}, Presidio: {presidio_value}")