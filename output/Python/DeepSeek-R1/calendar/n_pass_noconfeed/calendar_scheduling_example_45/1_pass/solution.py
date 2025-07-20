def main():
    # Work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0  # 9:00 in minutes (relative to 9:00)
    work_end = 480  # 17:00 (8 hours * 60 minutes)

    # Samuel's busy blocks in minutes relative to 9:00
    busy_blocks = [
        (0, 90),    # 9:00-10:30
        (150, 180), # 11:30-12:00
        (240, 270), # 13:00-13:30
        (300, 420), # 14:00-16:00
        (450, 480)  # 16:30-17:00
    ]

    # Calculate free intervals
    free_blocks = []
    current = work_start
    for start, end in busy_blocks:
        if current < start:
            free_blocks.append((current, start))
        current = end
    if current < work_end:
        free_blocks.append((current, work_end))

    # Find earliest 30-minute slot
    duration = 30
    meeting_start = None
    for start, end in free_blocks:
        if end - start >= duration:
            meeting_start = start
            break

    # Convert meeting time to HH:MM format
    start_hour = 9 + meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = 9 + (meeting_start + duration) // 60
    end_minute = (meeting_start + duration) % 60

    # Format the time string as HH:MM:HH:MM
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    # Output day and time range
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()