def main():
    # Define work hours (9:00 to 17:00) in minutes
    day_start = 9 * 60  # 540 minutes
    day_end = 17 * 60   # 1020 minutes

    # Collect all busy intervals in minutes (start, end)
    busy_intervals = []
    
    # Megan's schedule
    busy_intervals.append((9*60, 9*60+30))    # 9:00-9:30
    busy_intervals.append((10*60, 11*60))      # 10:00-11:00
    busy_intervals.append((12*60, 12*60+30))   # 12:00-12:30
    
    # Christine's schedule
    busy_intervals.append((9*60, 9*60+30))     # 9:00-9:30
    busy_intervals.append((11*60+30, 12*60))   # 11:30-12:00
    busy_intervals.append((13*60, 14*60))      # 13:00-14:00
    busy_intervals.append((15*60+30, 16*60+30)) # 15:30-16:30
    
    # Gabriel: free all day (no intervals)
    
    # Sara's schedule
    busy_intervals.append((11*60+30, 12*60))   # 11:30-12:00
    busy_intervals.append((14*60+30, 15*60))   # 14:30-15:00
    
    # Bruce's schedule
    busy_intervals.append((9*60+30, 10*60))    # 9:30-10:00
    busy_intervals.append((10*60+30, 12*60))    # 10:30-12:00
    busy_intervals.append((12*60+30, 14*60))    # 12:30-14:00
    busy_intervals.append((14*60+30, 15*60))    # 14:30-15:00
    busy_intervals.append((15*60+30, 16*60+30)) # 15:30-16:30
    
    # Kathryn's schedule
    busy_intervals.append((10*60, 15*60+30))    # 10:00-15:30
    busy_intervals.append((16*60, 16*60+30))    # 16:00-16:30
    
    # Billy's schedule
    busy_intervals.append((9*60, 9*60+30))      # 9:00-9:30
    busy_intervals.append((11*60, 11*60+30))    # 11:00-11:30
    busy_intervals.append((12*60, 14*60))       # 12:00-14:00
    busy_intervals.append((14*60+30, 15*60+30)) # 14:30-15:30

    # Sort intervals by start time
    sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if sorted_intervals:
        current_start, current_end = sorted_intervals[0]
        for interval in sorted_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
    
    # Calculate free intervals
    free_intervals = []
    prev_end = day_start
    
    for start, end in merged:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = end
    
    if prev_end < day_end:
        free_intervals.append((prev_end, day_end))
    
    # Find the first free interval of at least 30 minutes
    meeting_duration = 30
    for start_min, end_min in free_intervals:
        if end_min - start_min >= meeting_duration:
            meeting_start = start_min
            meeting_end = meeting_start + meeting_duration
            break
    
    # Convert meeting time to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    
    # Output the result
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()