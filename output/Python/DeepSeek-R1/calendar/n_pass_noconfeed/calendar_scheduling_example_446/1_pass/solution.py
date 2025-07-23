def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Busy intervals for each participant (start_minute, end_minute)
    busy_intervals = [
        # Megan
        (540, 570), (600, 660), (720, 750),
        # Christine
        (540, 570), (690, 720), (780, 840), (930, 990),
        # Sara
        (690, 720), (870, 900),
        # Bruce
        (570, 600), (630, 720), (750, 840), (870, 900), (930, 990),
        # Kathryn
        (600, 930), (960, 990),
        # Billy
        (540, 570), (660, 690), (720, 840), (870, 930)
    ]

    # Merge overlapping busy intervals
    if not busy_intervals:
        merged = []
    else:
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        merged = [sorted_busy[0]]
        for current_start, current_end in sorted_busy[1:]:
            last_start, last_end = merged[-1]
            if current_start <= last_end:
                merged[-1] = (last_start, max(last_end, current_end))
            else:
                merged.append((current_start, current_end))

    # Calculate free intervals within work hours
    free_intervals = []
    current_start = work_start

    for busy_start, busy_end in merged:
        if current_start < busy_start:
            free_intervals.append((current_start, busy_start))
        current_start = busy_end
    if current_start < work_end:
        free_intervals.append((current_start, work_end))

    # Find first free interval that fits the meeting duration
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    else:
        meeting_start = None
        meeting_end = None

    # Convert meeting time to HH:MM format
    if meeting_start is not None:
        start_hour = meeting_start // 60
        start_min = meeting_start % 60
        end_hour = meeting_end // 60
        end_min = meeting_end % 60
        time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        print("Monday " + time_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()