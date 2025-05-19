def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Laura's busy times in minutes since midnight for each day
    laura_busy = {
        'Monday': [(10*60 + 30, 11*60), (12*60 + 30, 13*60), (14*60 + 30, 15*60 + 30), (16*60, 17*60)],
        'Tuesday': [(9*60 + 30, 10*60), (11*60, 11*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)],
        'Wednesday': [(11*60 + 30, 12*60), (12*60 + 30, 13*60), (15*60 + 30, 16*60 + 30)],
        'Thursday': [(10*60 + 30, 11*60), (12*60, 13*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    }
    
    # Philip's busy times in minutes since midnight for each day
    philip_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60, 11*60), (11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60, 14*60 + 30), (15*60, 16*60 + 30)],
        'Wednesday': [(9*60, 10*60), (11*60, 12*60), (12*60 + 30, 16*60), (16*60 + 30, 17*60)],
        'Thursday': [(9*60, 10*60 + 30), (11*60, 12*60 + 30), (13*60, 17*60)]
    }
    
    meeting_duration = 60  # 1 hour in minutes
    
    # Iterate through each day (excluding Wednesday for Philip)
    for day in days:
        if day == 'Wednesday':
            continue  # Philip can't meet on Wednesday
        
        # Get busy intervals for both participants
        laura_day = laura_busy.get(day, [])
        philip_day = philip_busy.get(day, [])
        
        # Combine and sort all busy intervals
        all_busy = laura_day + philip_day
        all_busy.sort()
        
        # Find free intervals
        free_intervals = []
        prev_end = work_start
        
        for start, end in all_busy:
            if start > prev_end:
                free_intervals.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_intervals.append((prev_end, work_end))
        
        # Check each free interval for availability
        for start, end in free_intervals:
            available_duration = end - start
            if available_duration >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                print(f"{day}: {time_str}")
                return
    
    print("No suitable time found.")

find_meeting_time()