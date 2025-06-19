# Define the participants dictionary
participants = {
    "John": [(9, 11), (14, 16)],  # Time ranges for John (9-11, 14-16)
    "Alice": [(10, 12), (15, 17)],  # Time ranges for Alice (10-12, 15-17)
    "Bob": [(11, 13), (16, 18)]  # Time ranges for Bob (11-13, 16-18)
}

# Define the current time
current_time = 12  # Example time

# Define the meeting duration in hours
meeting_duration = 0.5

# Iterate through the participants' time ranges
for participant, time_ranges in participants.items():
    # Check if the current time is within any of the time ranges
    for start_time, end_time in time_ranges:
        # Calculate the end time for the meeting
        meeting_end_time = current_time + meeting_duration
        
        # Check if the meeting end time is within the participant's time range
        if start_time <= current_time < end_time and end_time >= meeting_end_time:
            # If the current time is within any of the time ranges, do something
            print(f"Current time {current_time} is within participant {participant}'s time range")
            break
    else:
        # If the current time is not within any of the time ranges, do something else
        continue
    break
else:
    # If the current time is not within any participant's time range, do something else
    print(f"Current time {current_time} is not within any participant's time range")