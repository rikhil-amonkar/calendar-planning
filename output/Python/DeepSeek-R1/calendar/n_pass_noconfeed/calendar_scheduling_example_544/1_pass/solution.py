def main():
    # Work hours: 9:00 to 17:00
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes

    # Albert's blocked periods in minutes
    albert_blocked = [
        (9 * 60, 10 * 60),        # 9:00-10:00
        (10 * 60 + 30, 12 * 60),  # 10:30-12:00
        (15 * 60, 16 * 60 + 30)   # 15:00-16:30
    ]
    # Sort blocked periods by start time
    albert_blocked.sort(key=lambda x: x[0])
    
    # Find free intervals for Albert within work hours
    free_intervals = []
    current = work_start
    for block_start, block_end in albert_blocked:
        if current < block_start:
            free_intervals.append((current, block_start))
        current = max(current, block_end)
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Additional constraint: meeting must end by 11:00 (660 minutes)
    meeting_duration = 30
    candidate = None
    for start, end in free_intervals:
        # The meeting must end by min(end, 660)
        latest_end = min(end, 660)
        if latest_end - start >= meeting_duration:
            candidate = (start, start + meeting_duration)
            break
    
    if candidate is None:
        print("No suitable time found")
    else:
        start_min, end_min = candidate
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_hour = end_min // 60
        end_minute = end_min % 60
        time_str = f"{start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}"
        print("Monday")
        print(time_str)

if __name__ == "__main__":
    main()