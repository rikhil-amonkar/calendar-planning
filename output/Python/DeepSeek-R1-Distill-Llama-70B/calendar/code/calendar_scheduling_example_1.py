def find_meeting_time():
    # Define the work hours
    work_hours = {
        "start": 9,
        "end": 17
    }

    # Define participants' schedules
    raymond_schedule = [[9, 9.5], [11.5, 12], [13, 13.5], [15, 15.5]]
    billy_schedule = [[10, 10.5], [12, 13], [16.5, 17]]
    donald_schedule = [[9, 9.5], [10, 11], [12, 13], [14, 14.5], [16, 17]]

    # Combine all schedules
    all_schedules = [
        raymond_schedule,
        billy_schedule,
        donald_schedule
    ]

    # Flatten and sort all busy intervals
    all_busy = []
    for schedule in all_schedules:
        all_busy.extend(schedule)
    all_busy.sort(key=lambda x: x[0])

    # Initialize previous end time to work hours start
    prev_end = work_hours["start"]

    # Billy's preference: avoid meetings after 15:00
    billy_preference = 15

    # Apply Billy's preference
    if prev_end < billy_preference:
        prev_end = billy_preference

    # Iterate through each busy interval
    for busy_start, busy_end in all_busy:
        # Check for available slot before the busy interval starts
        if busy_start - prev_end >= 0.5:  # 0.5 hours = 30 minutes
            # Format the time slots
            start_time = prev_end
            end_time = prev_end + 0.5
            # Convert to HH:MM format
            start_hh = int(start_time)
            start_mm = int((start_time - start_hh) * 60)
            end_hh = int(end_time)
            end_mm = int((end_time - end_hh) * 60)
            # Return the earliest available time
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d} on Monday"
        
        # Update previous end time
        prev_end = max(prev_end, busy_end)

    # Check for available slot after the last busy interval
    if work_hours["end"] - prev_end >= 0.5:
        start_time = prev_end
        end_time = prev_end + 0.5
        start_hh = int(start_time)
        start_mm = int((start_time - start_hh) * 60)
        end_hh = int(end_time)
        end_mm = int((end_time - end_hh) * 60)
        return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d} on Monday"

    # If no time found (should not happen as per problem statement)
    return "No available time found"

# Execute the function
print(find_meeting_time())