def find_meeting_time():
    # Define work hours and days
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Define busy times for Natalie and William in minutes since midnight
    natalie_busy = {
        'Monday': [(9*60, 9*60 + 30), (10*60, 12*60), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60, 16*60 + 30)],
        'Tuesday': [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (12*60 + 30, 14*60), (16*60, 17*60)],
        'Wednesday': [(11*60, 11*60 + 30), (16*60, 16*60 + 30)],
        'Thursday': [(10*60, 11*60), (11*60 + 30, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
    }
    
    william_busy = {
        'Monday': [(9*60 + 30, 11*60), (11*60 + 30, 17*60)],
        'Tuesday': [(9*60, 13*60), (13*60 + 30, 16*60)],
        'Wednesday': [(9*60, 12*60 + 30), (13*60, 14*60 + 30), (15*60 + 30, 16*60), (16*60 + 30, 17*60)],
        'Thursday': [(9*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 14*60), (15*60, 17*60)]
    }
    
    meeting_duration = 60  # 1 hour in minutes
    
    for day in days:
        # Combine and sort all busy intervals for both participants
        combined_busy = natalie_busy.get(day, []) + william_busy.get(day, [])
        combined_busy.sort()
        
        # Find free intervals
        free_intervals = []
        prev_end = work_hours_start
        
        for start, end in combined_busy:
            if start > prev_end:
                free_intervals.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_hours_end:
            free_intervals.append((prev_end, work_hours_end))
        
        # Check if any free interval is long enough
        for start, end in free_intervals:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_hh = meeting_start // 60
                start_mm = meeting_start % 60
                end_hh = meeting_end // 60
                end_mm = meeting_end % 60
                return f"{day}, {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    
    return "No suitable time found."

# Run the function and print the result
print(find_meeting_time())