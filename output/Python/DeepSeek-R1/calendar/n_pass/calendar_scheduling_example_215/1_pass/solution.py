def main():
    day = "Monday"
    start_work = 9 * 60  # 9:00 in minutes
    end_work = 17 * 60   # 17:00 in minutes
    total_minutes = end_work - start_work  # 480 minutes
    timeline = [False] * total_minutes  # False means free, True means busy
    
    # Define busy intervals in minutes relative to 9:00 (0 minutes)
    # Cynthia's busy intervals
    cynthia_busy = [(30, 90), (150, 180), (240, 270), (360, 420)]
    # Lauren's busy intervals
    lauren_busy = [(0, 30), (90, 120), (150, 180), (240, 270), (300, 330), (360, 390), (420, 480)]
    # Robert's busy intervals
    robert_busy = [(90, 120), (150, 180), (210, 270), (300, 420)]
    
    # Mark busy times in the timeline
    for start, end in cynthia_busy:
        for minute in range(start, min(end, total_minutes)):
            timeline[minute] = True
    for start, end in lauren_busy:
        for minute in range(start, min(end, total_minutes)):
            timeline[minute] = True
    for start, end in robert_busy:
        for minute in range(start, min(end, total_minutes)):
            timeline[minute] = True
    
    # Find earliest 30-minute free slot
    meeting_duration = 30
    start_minute = -1
    for s in range(total_minutes - meeting_duration + 1):
        if all(not timeline[s + i] for i in range(meeting_duration)):
            start_minute = s
            break
    
    # Convert start_minute to absolute time
    total_minutes_start = start_work + start_minute
    start_hour = total_minutes_start // 60
    start_min = total_minutes_start % 60
    total_minutes_end = total_minutes_start + meeting_duration
    end_hour = total_minutes_end // 60
    end_min = total_minutes_end % 60
    
    # Format the output
    time_range_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print(day)
    print(time_range_str)

if __name__ == "__main__":
    main()