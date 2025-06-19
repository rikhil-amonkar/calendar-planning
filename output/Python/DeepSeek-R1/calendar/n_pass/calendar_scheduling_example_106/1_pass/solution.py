def main():
    # Convert work hours to minutes (9:00 to 17:00)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    meeting_duration = 60  # 60 minutes

    # Define busy intervals for each participant in minutes (start inclusive, end exclusive)
    olivia = [
        (12*60 + 30, 13*60 + 30),  # 12:30-13:30
        (14*60 + 30, 15*60),        # 14:30-15:00
        (16*60 + 30, 17*60)         # 16:30-17:00
    ]
    anna = []  # No meetings
    virginia = [
        (9*60, 10*60),              # 9:00-10:00
        (11*60 + 30, 16*60),        # 11:30-16:00
        (16*60 + 30, 17*60)         # 16:30-17:00
    ]
    paul = [
        (9*60, 9*60 + 30),          # 9:00-9:30
        (11*60, 11*60 + 30),        # 11:00-11:30
        (13*60, 14*60),             # 13:00-14:00
        (14*60 + 30, 16*60),        # 14:30-16:00
        (16*60 + 30, 17*60)         # 16:30-17:00
    ]

    # Combine all busy intervals
    all_busy = olivia + anna + virginia + paul

    # Sort busy intervals by start time
    sorted_busy = sorted(all_busy, key=lambda x: x[0])
    merged = []
    if sorted_busy:
        start_curr, end_curr = sorted_busy[0]
        for i in range(1, len(sorted_busy)):
            s, e = sorted_busy[i]
            if s <= end_curr:
                if e > end_curr:
                    end_curr = e
            else:
                merged.append((start_curr, end_curr))
                start_curr, end_curr = s, e
        merged.append((start_curr, end_curr))

    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for interval in merged:
        s, e = interval
        if s > current:
            free_intervals.append((current, s))
        current = max(current, e)
    if current < work_end:
        free_intervals.append((current, work_end))

    # Find first free interval with sufficient duration
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            break

    if meeting_start is None:
        meeting_start = work_start  # Fallback (shouldn't occur per problem)

    meeting_end = meeting_start + meeting_duration

    # Convert meeting times to formatted strings (HH:MM)
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60

    # Format without leading zero for single-digit hours
    time_str = f"{start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}, Monday"
    print(time_str)

if __name__ == "__main__":
    main()