def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    
    # Define all busy intervals in minutes (start, end)
    busy_intervals = [
        [570, 600],   # Jeffrey: 9:30-10:00
        [630, 660],   # Jeffrey: 10:30-11:00
        [540, 570],   # Virginia: 9:00-9:30
        [600, 630],   # Virginia: 10:00-10:30
        [870, 900],   # Virginia: 14:30-15:00
        [960, 990],   # Virginia: 16:00-16:30
        [540, 690],   # Melissa: 9:00-11:30
        [720, 750],   # Melissa: 12:00-12:30
        [780, 900],   # Melissa: 13:00-15:00
        [960, 1020]   # Melissa: 16:00-17:00
    ]
    
    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping busy intervals
    merged = []
    current_start, current_end = busy_intervals[0]
    for interval in busy_intervals[1:]:
        if interval[0] <= current_end:
            current_end = max(current_end, interval[1])
        else:
            merged.append([current_start, current_end])
            current_start, current_end = interval
    merged.append([current_start, current_end])
    
    # Calculate free intervals within work hours
    free_intervals = []
    prev_end = work_start
    for interval in merged:
        start, end = interval
        if start > prev_end:
            free_intervals.append([prev_end, start])
        prev_end = end
    if prev_end < work_end:
        free_intervals.append([prev_end, work_end])
    
    # Find a meeting slot (30 minutes) that ends by 14:00 (840 minutes) if possible
    candidate = None
    preference_end = 14 * 60  # 840 minutes (14:00)
    for interval in free_intervals:
        start_free, end_free = interval
        # Check if meeting fits and ends by 14:00
        if start_free + 30 <= min(end_free, preference_end):
            candidate = start_free
            break
    
    # If no candidate found in preference pass, find any 30-minute slot
    if candidate is None:
        for interval in free_intervals:
            start_free, end_free = interval
            if end_free - start_free >= 30:
                candidate = start_free
                break
    
    # Convert candidate time to HH:MM format
    start_hour = candidate // 60
    start_minute = candidate % 60
    end_minutes = candidate + 30
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    # Format as HH:MM:HH:MM
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    # Output the day and time string
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()