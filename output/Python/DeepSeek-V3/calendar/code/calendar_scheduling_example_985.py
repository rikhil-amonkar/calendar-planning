def find_meeting_time():
    # Define work hours and days
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Define busy intervals for each person per day in minutes since midnight
    diane_busy = {
        'Monday': [(12 * 60, 12 * 60 + 30), (15 * 60, 15 * 60 + 30)],
        'Tuesday': [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (16 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 9 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
        'Thursday': [(15 * 60 + 30, 16 * 60 + 30)],
        'Friday': [(9 * 60 + 30, 11 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
    }
    
    matthew_busy = {
        'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 11 * 60), (12 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
        'Thursday': [(9 * 60, 16 * 60)],
        'Friday': [(9 * 60, 17 * 60)]
    }
    
    # Matthew's preference: not before 12:30 on Wednesday
    matthew_preference = {
        'Wednesday': 12 * 60 + 30
    }
    
    meeting_duration = 60  # 1 hour in minutes
    
    for day in days:
        # Check if day is Wednesday and apply Matthew's preference
        if day == 'Wednesday':
            start_candidate = max(work_start, matthew_preference.get(day, work_start))
        else:
            start_candidate = work_start
        
        # Collect all busy intervals for the day
        busy_intervals = []
        if day in diane_busy:
            busy_intervals.extend(diane_busy[day])
        if day in matthew_busy:
            busy_intervals.extend(matthew_busy[day])
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find free slots
        current_time = start_candidate
        for interval in busy_intervals:
            if interval[0] > current_time:
                # Check if there's enough time before the next busy interval
                if interval[0] - current_time >= meeting_duration:
                    # Found a suitable slot
                    start_time = current_time
                    end_time = start_time + meeting_duration
                    # Format the time as HH:MM
                    start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
                    end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
                    print(f"{start_str}:{end_str}")
                    print(day)
                    return
            # Update current_time to the end of the current busy interval
            current_time = max(current_time, interval[1])
        
        # Check after the last busy interval
        if work_end - current_time >= meeting_duration:
            start_time = current_time
            end_time = start_time + meeting_duration
            start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
            end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
            print(f"{start_str}:{end_str}")
            print(day)
            return
    
    print("No suitable time found.")

find_meeting_time()