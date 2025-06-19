def main():
    # Meeting duration is 30 minutes
    duration = 30

    # Since Nathan cannot meet on Monday and Amanda doesn't want Tuesday after 11:00, we only consider Tuesday from 9:00 to 11:00
    day = "Tuesday"
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 11 * 60   # 11:00 in minutes

    # Define busy intervals for Tuesday within 9:00-11:00 (in minutes)
    amanda_busy = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (10 * 60, 10 * 60 + 30)   # 10:00-10:30
    ]
    nathan_busy = [
        (9 * 60, 10 * 60 + 30)    # 9:00-10:30
    ]

    # Combine and sort all busy intervals
    all_busy = amanda_busy + nathan_busy
    all_busy.sort(key=lambda x: x[0])

    # Merge overlapping busy intervals
    merged = []
    for start, end in all_busy:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1] = (last_start, max(last_end, end))
            else:
                merged.append((start, end))

    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))

    # Find the first free interval that can fit the meeting
    meeting_start = None
    meeting_end = None
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = start + duration
            break

    # Convert meeting time to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)

    # Output day and time in the specified format
    print(day)
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()