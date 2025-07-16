def main():
    # Work hours: 9:00 to 17:00
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes

    # Samuel's busy intervals in minutes
    busy_samuel = [
        (9 * 60, 10 * 60 + 30),    # 9:00 to 10:30
        (11 * 60 + 30, 12 * 60),   # 11:30 to 12:00
        (13 * 60, 13 * 60 + 30),   # 13:00 to 13:30
        (14 * 60, 16 * 60),        # 14:00 to 16:00
        (16 * 60 + 30, 17 * 60)    # 16:30 to 17:00
    ]
    
    # Sort the busy intervals by start time (though they are already sorted)
    busy_samuel.sort()
    
    # Calculate free intervals
    free_intervals = []
    current = work_start
    for start, end in busy_samuel:
        if current < start:
            free_intervals.append((current, start))
        current = end
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Duration of the meeting in minutes
    duration = 30
    
    # Find the earliest free interval that can accommodate the meeting
    meeting_start = None
    meeting_end = None
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = start + duration
            break
    
    # Convert meeting times back to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60
    
    # Format as two-digit strings
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    print(time_str)
    print("Monday")

if __name__ == "__main__":
    main()