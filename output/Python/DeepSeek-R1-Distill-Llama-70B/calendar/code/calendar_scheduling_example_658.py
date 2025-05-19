def find_meeting_time():
    # Define the work hours
    work_hours = {
        "start": 9,
        "end": 17
    }

    # Define participants' schedules
    shirley_schedule = {
        "Monday": [[10.5, 11], [12, 12.5], [16, 16.5]],
        "Tuesday": [[9.5, 10]]
    }

    albert_schedule = {
        "Monday": [[9, 17]],
        "Tuesday": [[9.5, 11], [11.5, 12.5], [13, 16], [16.5, 17]]
    }

    # Define the meeting duration
    meeting_duration = 0.5  # In hours (30 minutes)

    # Define the days to check
    days_to_check = ["Monday", "Tuesday"]

    # Shirley's preference: rather not meet on Tuesday after 10:30
    shirley_preference = {
        "Tuesday": 10.5
    }

    # Iterate through each day
    for day in days_to_check:
        # Combine and sort all busy intervals for both participants
        shirley_busy = shirley_schedule[day]
        albert_busy = albert_schedule[day]
        all_busy = sorted(shirley_busy + albert_busy, key=lambda x: x[0])

        # Initialize previous end time to work hours start
        prev_end = work_hours["start"]

        # Apply Shirley's preference for Tuesday
        if day == "Tuesday" and prev_end < shirley_preference[day]:
            prev_end = shirley_preference[day]

        # Iterate through each busy interval
        for busy_start, busy_end in all_busy:
            # Check for available slot before the busy interval starts
            if busy_start - prev_end >= meeting_duration:
                # Format the time slots
                start_time = prev_end
                end_time = prev_end + meeting_duration
                # Convert to HH:MM format
                start_hh = int(start_time)
                start_mm = int((start_time - start_hh) * 60)
                end_hh = int(end_time)
                end_mm = int((end_time - end_hh) * 60)
                # Return the earliest available time
                return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d} on {day}"
            
            # Update previous end time
            prev_end = max(prev_end, busy_end)

        # Check for available slot after the last busy interval
        if work_hours["end"] - prev_end >= meeting_duration:
            start_time = prev_end
            end_time = prev_end + meeting_duration
            start_hh = int(start_time)
            start_mm = int((start_time - start_hh) * 60)
            end_hh = int(end_time)
            end_mm = int((end_time - end_hh) * 60)
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d} on {day}"

    # If no time found (should not happen as per problem statement)
    return "No available time found"

# Execute the function
print(find_meeting_time())