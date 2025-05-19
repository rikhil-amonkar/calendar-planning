def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy times for each participant in minutes since midnight
    tyler_busy = {
        'Tuesday': [(9*60, 9*60 + 30), (14*60 + 30, 15*60)],
        'Wednesday': [(10*60 + 30, 11*60), (12*60 + 30, 13*60), (13*60 + 30, 14*60), (16*60 + 30, 17*60)],
    }
    ruth_busy = {
        'Monday': [(9*60, 10*60), (10*60 + 30, 12*60), (12*60 + 30, 14*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 17*60)],
    }
    # Tyler's preference: avoid Monday before 16:00
    tyler_preference = {
        'Monday': (9*60, 16*60)
    }

    # Iterate through each day
    for day in days:
        if day == 'Monday' and day in tyler_preference:
            # On Monday, only consider times after 16:00 due to Tyler's preference
            start_time = max(work_start, tyler_preference[day][1])
        else:
            start_time = work_start

        # Generate all possible slots for the day
        current_time = start_time
        while current_time + meeting_duration <= work_end:
            slot_end = current_time + meeting_duration
            # Check if the slot is free for both Tyler and Ruth
            tyler_free = True
            ruth_free = True

            # Check Tyler's busy times
            if day in tyler_busy:
                for busy_start, busy_end in tyler_busy[day]:
                    if not (slot_end <= busy_start or current_time >= busy_end):
                        tyler_free = False
                        break

            # Check Ruth's busy times
            if day in ruth_busy:
                for busy_start, busy_end in ruth_busy[day]:
                    if not (slot_end <= busy_start or current_time >= busy_end):
                        ruth_free = False
                        break

            if tyler_free and ruth_free:
                # Format the time as HH:MM:HH:MM
                start_hh = current_time // 60
                start_mm = current_time % 60
                end_hh = slot_end // 60
                end_mm = slot_end % 60
                return f"{day}: {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"

            current_time += 15  # Check in 15-minute increments

    return "No suitable time found"

# Run the function and print the result
print(find_meeting_time())