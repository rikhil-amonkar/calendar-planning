def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy slots for each participant per day in minutes since midnight
    cheryl_busy = {
        'Monday': [(9*60, 9*60 + 30), (11*60 + 30, 13*60), (15*60 + 30, 16*60)],
        'Tuesday': [(15*60, 15*60 + 30)],
        'Wednesday': []  # Cheryl cannot meet on Wednesday
    }
    
    kyle_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60 + 30, 17*60)],
        'Wednesday': [(9*60, 9*60 + 30), (10*60, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 17*60)]
    }

    # Iterate through each day to find a suitable time
    for day in days:
        if day == 'Wednesday':
            continue  # Cheryl cannot meet on Wednesday
        
        # Combine and sort all busy slots for the day
        all_busy = cheryl_busy[day] + kyle_busy[day]
        all_busy.sort()

        # Initialize previous end time as work start
        prev_end = work_start

        # Check gaps between busy slots
        for busy_start, busy_end in all_busy:
            if busy_start > prev_end:
                # Found a gap, check if it's long enough
                if busy_start - prev_end >= meeting_duration:
                    # Format the time as HH:MM:HH:MM
                    start_hh = prev_end // 60
                    start_mm = prev_end % 60
                    end_hh = (prev_end + meeting_duration) // 60
                    end_mm = (prev_end + meeting_duration) % 60
                    time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                    return day, time_str
            prev_end = max(prev_end, busy_end)

        # Check after the last busy slot
        if work_end - prev_end >= meeting_duration:
            start_hh = prev_end // 60
            start_mm = prev_end % 60
            end_hh = (prev_end + meeting_duration) // 60
            end_mm = (prev_end + meeting_duration) % 60
            time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return day, time_str

    return "No meeting time found", ""

day, time_str = find_meeting_time()
print(f"{day}: {time_str}")