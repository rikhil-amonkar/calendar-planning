def main():
    # Work hours: 9:00 to 17:00
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    meeting_duration = 30  # minutes

    # Nicole's busy intervals in minutes (start, end)
    nicole_busy = [
        (9 * 60, 10 * 60),       # 9:00 to 10:00
        (10 * 60 + 30, 16 * 60 + 30)  # 10:30 to 16:30
    ]

    # Sort busy intervals by start time
    nicole_busy_sorted = sorted(nicole_busy, key=lambda x: x[0])
    
    # Compute Nicole's free intervals within work hours
    free_intervals = []
    current_time = work_start
    for start, end in nicole_busy_sorted:
        if current_time < start:
            free_intervals.append((current_time, start))
        current_time = max(current_time, end)
    if current_time < work_end:
        free_intervals.append((current_time, work_end))
    
    # Find a meeting slot that is at least meeting_duration long and starts at or after 16:00 (960 minutes)
    candidate = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            if start >= 16 * 60:  # 16:00 in minutes
                candidate = (start, start + meeting_duration)
                break
    if candidate is None:
        for start, end in free_intervals:
            if end - start >= meeting_duration:
                candidate = (start, start + meeting_duration)
                break
    
    # Convert candidate start and end times to HH:MM format
    start_min, end_min = candidate
    start_hour = start_min // 60
    start_minute = start_min % 60
    end_hour = end_min // 60
    end_minute = end_min % 60
    
    start_str = f"{start_hour:02d}:{start_minute:02d}"
    end_str = f"{end_hour:02d}:{end_minute:02d}"
    
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()