def main():
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0
    work_end = 480  # 17:00 is 8 hours after 9:00 (480 minutes)
    
    # List all busy intervals (in minutes from 9:00)
    busy_intervals = []
    
    # Cynthia's busy times
    busy_intervals.append((30, 90))    # 9:30-10:30
    busy_intervals.append((150, 180))  # 11:30-12:00
    busy_intervals.append((240, 270))  # 13:00-13:30
    busy_intervals.append((360, 420))  # 15:00-16:00
    
    # Lauren's busy times
    busy_intervals.append((0, 30))     # 9:00-9:30
    busy_intervals.append((90, 120))   # 10:30-11:00
    busy_intervals.append((150, 180))  # 11:30-12:00
    busy_intervals.append((240, 270))  # 13:00-13:30
    busy_intervals.append((300, 330))  # 14:00-14:30
    busy_intervals.append((360, 390))  # 15:00-15:30
    busy_intervals.append((420, 480))  # 16:00-17:00
    
    # Robert's busy times
    busy_intervals.append((90, 120))   # 10:30-11:00
    busy_intervals.append((150, 180))  # 11:30-12:00
    busy_intervals.append((210, 270))  # 12:30-13:30
    busy_intervals.append((300, 420))  # 14:00-16:00
    
    # Steven and Roy have no busy times
    
    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            s, e = interval
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free intervals
    free_intervals = []
    start = work_start
    for interval in merged:
        if start < interval[0]:
            free_intervals.append((start, interval[0]))
        start = interval[1]
    if start < work_end:
        free_intervals.append((start, work_end))
    
    # Find the earliest free interval of at least 30 minutes
    meeting_start = None
    for s, e in free_intervals:
        if e - s >= 30:
            meeting_start = s
            meeting_end = s + 30
            break
    
    # Convert meeting time to HH:MM format
    start_hour = 9 + meeting_start // 60
    start_min = meeting_start % 60
    end_hour = 9 + meeting_end // 60
    end_min = meeting_end % 60
    
    # Format the time string as HH:MM:HH:MM
    time_str = f"{start_hour}:{start_min:02d}:{end_hour}:{end_min:02d}"
    
    # Output day and time string
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()