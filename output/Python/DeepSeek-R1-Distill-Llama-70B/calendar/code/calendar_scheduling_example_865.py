def find_meeting_time():
    # Define the work hours
    work_hours = {
        "start": 9,
        "end": 17
    }

    # Define participants' schedules
    megan_schedule = {
        "Monday": [[13, 13.5], [14, 15.5]],
        "Tuesday": [[9, 9.5], [12, 12.5], [16, 17]],
        "Wednesday": [[9.5, 10], [10.5, 11.5], [12.5, 14], [16, 16.5]],
        "Thursday": [[13.5, 14.5], [15, 15.5]]
    }

    daniel_schedule = {
        "Monday": [[10, 11.5], [12.5, 15]],
        "Tuesday": [[9, 10], [10.5, 17]],
        "Wednesday": [[9, 10], [10.5, 11.5], [12, 17]],
        "Thursday": [[9, 12], [12.5, 14.5], [15, 15.5], [16, 17]]
    }

    # Define the meeting duration
    meeting_duration = 1.0  # In hours (1 hour)

    # Define the days to check
    days_to_check = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    # Iterate through each day
    for day in days_to_check:
        # Combine and sort all busy intervals for both participants
        megan_busy = megan_schedule[day]
        daniel_busy = daniel_schedule[day]
        all_busy = sorted(megan_busy + daniel_busy, key=lambda x: x[0])

        # Initialize previous end time to work hours start
        prev_end = work_hours["start"]

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