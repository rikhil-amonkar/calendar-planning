def find_meeting_time():
    # Define the work hours
    work_hours = {
        "start": 9,
        "end": 17
    }

    # Define participants' schedules
    bryan_schedule = {
        "Thursday": [[9.5, 10], [12.5, 13]],
        "Friday": [[10.5, 11], [14, 14.5]]
    }

    nicholas_schedule = {
        "Monday": [[11.5, 12]],
        "Tuesday": [[9, 9.5], [11, 13.5], [14, 16.5]],
        "Wednesday": [[9, 9.5], [10, 11], [11.5, 13.5], [14, 14.5], [15, 16.5]],
        "Thursday": [[10.5, 11.5], [12, 12.5], [15, 15.5], [16.5, 17]],
        "Friday": [[9, 10.5], [11, 12], [12.5, 14.5], [15.5, 16], [16.5, 17]]
    }

    # Define the meeting duration
    meeting_duration = 1.0  # In hours (1 hour)

    # Define the days to check (Bryan avoids Tuesday, Nicholas avoids Monday and Thursday)
    days_to_check = ["Wednesday", "Friday"]

    # Iterate through each day
    for day in days_to_check:
        # Get schedules for the current day
        bryan_busy = bryan_schedule.get(day, [])
        nicholas_busy = nicholas_schedule.get(day, [])

        # Combine and sort all busy intervals for both participants
        all_busy = sorted(bryan_busy + nicholas_busy, key=lambda x: x[0])

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