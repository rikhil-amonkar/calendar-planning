def find_meeting_time():
    # Define the work hours
    work_hours = {
        "start": 9,
        "end": 17
    }

    # Define participants' schedules
    susan_schedule = {
        "Monday": [[12.5, 13], [13.5, 14]],
        "Tuesday": [[11.5, 12]],
        "Wednesday": [[9.5, 10.5], [14, 14.5], [15.5, 16.5]]
    }

    sandra_schedule = {
        "Monday": [[9, 13], [14, 15], [16, 16.5]],
        "Tuesday": [[9, 9.5], [10.5, 12], [12.5, 13.5], [14, 14.5], [16, 17]],
        "Wednesday": [[9, 11.5], [12, 12.5], [13, 17]]
    }

    # Define the meeting duration
    meeting_duration = 0.5  # In hours (30 minutes)

    # Define the days to check (Susan rather not meet on Tuesday)
    days_to_check = ["Monday", "Wednesday"]

    # Sandra's constraint: can not meet on Monday after 16:00
    sandra_constraint = {
        "Monday": 16
    }

    # Iterate through each day
    for day in days_to_check:
        # Apply Sandra's constraint for Monday
        if day == "Monday":
            sandra_busy = [interval for interval in sandra_schedule[day] if interval[1] <= sandra_constraint[day]]
        else:
            sandra_busy = sandra_schedule[day]

        # Combine and sort all busy intervals for both participants
        susan_busy = susan_schedule[day]
        all_busy = sorted(susan_busy + sandra_busy, key=lambda x: x[0])

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