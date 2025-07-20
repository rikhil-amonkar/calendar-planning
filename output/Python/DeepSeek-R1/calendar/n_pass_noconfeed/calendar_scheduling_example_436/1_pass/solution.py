def main():
    work_start_min = 9 * 60  # 9:00 in minutes
    work_end_min = 17 * 60   # 17:00 in minutes
    meeting_duration = 30    # 30 minutes

    # Define all busy intervals in minutes (start, end)
    busy_intervals = []
    
    # Patrick's meetings
    busy_intervals.append((13*60 + 30, 14*60))    # 13:30-14:00
    busy_intervals.append((14*60 + 30, 15*60))    # 14:30-15:00
    
    # Shirley's meetings
    busy_intervals.append((9*60, 9*60 + 30))      # 9:00-9:30
    busy_intervals.append((11*60, 11*60 + 30))    # 11:00-11:30
    busy_intervals.append((12*60, 12*60 + 30))    # 12:00-12:30
    busy_intervals.append((14*60 + 30, 15*60))    # 14:30-15:00
    busy_intervals.append((16*60, 17*60))         # 16:00-17:00
    
    # Jeffrey's meetings
    busy_intervals.append((9*60, 9*60 + 30))      # 9:00-9:30
    busy_intervals.append((10*60 + 30, 11*60))    # 10:30-11:00
    busy_intervals.append((11*60 + 30, 12*60))    # 11:30-12:00
    busy_intervals.append((13*60, 13*60 + 30))    # 13:00-13:30
    busy_intervals.append((16*60, 17*60))         # 16:00-17:00
    
    # Gloria's meetings
    busy_intervals.append((11*60 + 30, 12*60))    # 11:30-12:00
    busy_intervals.append((15*60, 15*60 + 30))    # 15:00-15:30
    
    # Nathan's meetings
    busy_intervals.append((9*60, 9*60 + 30))      # 9:00-9:30
    busy_intervals.append((10*60 + 30, 12*60))    # 10:30-12:00
    busy_intervals.append((14*60, 17*60))         # 14:00-17:00
    
    # Angela's meetings
    busy_intervals.append((9*60, 9*60 + 30))      # 9:00-9:30
    busy_intervals.append((10*60, 11*60))         # 10:00-11:00
    busy_intervals.append((12*60 + 30, 15*60))    # 12:30-15:00
    busy_intervals.append((15*60 + 30, 16*60 + 30)) # 15:30-16:30
    
    # David's meetings
    busy_intervals.append((9*60, 9*60 + 30))      # 9:00-9:30
    busy_intervals.append((10*60, 10*60 + 30))    # 10:00-10:30
    busy_intervals.append((11*60, 14*60))         # 11:00-14:00
    busy_intervals.append((14*60 + 30, 16*60 + 30)) # 14:30-16:30
    
    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free time gaps
    free_gaps = []
    current = work_start_min
    for s, e in merged:
        if current < s:
            gap_start = current
            gap_end = s
            if gap_end - gap_start >= meeting_duration:
                free_gaps.append((gap_start, gap_end))
            current = e
        else:
            current = max(current, e)
    if current < work_end_min:
        gap_start = current
        gap_end = work_end_min
        if gap_end - gap_start >= meeting_duration:
            free_gaps.append((gap_start, gap_end))
    
    # Select the earliest free gap of sufficient duration
    if free_gaps:
        gap_start, gap_end = free_gaps[0]
        meeting_start = gap_start
        meeting_end = meeting_start + meeting_duration
        
        # Format meeting times to HH:MM
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_str = format_time(meeting_start)
        end_str = format_time(meeting_end)
        
        # Output in the specified format: Day HH:MM:HH:MM
        print(f"Monday {start_str}:{end_str}")
    else:
        # Fallback if no slot found (should not occur per problem)
        print("Monday 00:00:00:00")

if __name__ == "__main__":
    main()