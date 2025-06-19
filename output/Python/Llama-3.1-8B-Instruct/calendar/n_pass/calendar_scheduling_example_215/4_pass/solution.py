# Define the participants dictionary
participants = {
    "John": [(9, 12), (14, 16)],  # Time ranges for John
    "Alice": [(10, 13), (15, 17)],  # Time ranges for Alice
    "Bob": [(11, 14), (16, 18)]  # Time ranges for Bob
}

# Define the current time
current_time = 12  # Example time

for participant, time_ranges in participants.items():
    if any(start_time <= current_time < end_time for start_time, end_time in time_ranges):
        # If the current time is within any of the time ranges, do something
        print(f"Current time {current_time} is within participant {participant}'s time range")
        break
else:
    # If the current time is not within any of the time ranges, do something else
    print(f"Current time {current_time} is not within any participant's time range")