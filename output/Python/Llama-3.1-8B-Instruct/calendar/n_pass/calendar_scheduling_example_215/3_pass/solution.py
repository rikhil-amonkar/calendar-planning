for participant in participants:
    if any(start_time <= current_time < end_time for start_time, end_time in participants[participant]):
        # If the current time is within any of the time ranges, do something
        print(f"Current time {current_time} is within participant {participant}'s time range")
        break
else:
    # If the current time is not within any of the time ranges, do something else
    print(f"Current time {current_time} is not within any participant's time range")