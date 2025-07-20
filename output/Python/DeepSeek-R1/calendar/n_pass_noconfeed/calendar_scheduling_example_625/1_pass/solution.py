def main():
    # Work hours: 9:00 to 17:00 (converted to minutes)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    
    # Harold's preferences: avoid Monday, avoid Tuesday before 14:30 (870 minutes)
    start_after = 14 * 60 + 30  # 870 minutes (14:30)
    
    # Harold's busy intervals on Tuesday (in minutes since midnight) within work hours
    tuesday_busy = [
        (540, 570),   # 9:00-9:30
        (630, 690),   # 10:30-11:30
        (750, 810),   # 12:30-13:30
        (870, 930),   # 14:30-15:30
        (960, 1020)   # 16:00-17:00
    ]
    
    # Focus on time window: Tuesday after 14:30 until work_end
    intervals_afternoon = []
    for s, e in tuesday_busy:
        if e <= start_after:
            continue
        if s >= work_end:
            continue
        s_adjusted = max(s, start_after)
        e_adjusted = min(e, work_end)
        if s_adjusted < e_adjusted:
            intervals_afternoon.append((s_adjusted, e_adjusted))
    
    # Calculate free intervals in the afternoon
    free_intervals = []
    current = start_after
    for s, e in sorted(intervals_afternoon, key=lambda x: x[0]):
        if current < s:
            free_intervals.append((current, s))
        current = max(current, e)
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Find the first free interval >= 30 minutes
    meeting_duration = 30
    for start_min, end_min in free_intervals:
        if end_min - start_min >= meeting_duration:
            # Convert start and end times to HH:MM format
            def format_time(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"
            
            start_str = format_time(start_min)
            end_str = format_time(start_min + meeting_duration)
            print("Tuesday")
            print(f"{start_str}:{end_str}")
            return
    
    # Fallback (shouldn't be reached as solution exists)
    print("No suitable time found")

if __name__ == "__main__":
    main()