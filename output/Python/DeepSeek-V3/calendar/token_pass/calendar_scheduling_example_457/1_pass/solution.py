def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 9:00."""
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    """Convert minutes from 9:00 back to HH:MM."""
    h = 9 + m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Work hours in minutes from 9:00
    work_start = 0          # 9:00
    work_end = 8 * 60       # 17:00 = 480 minutes from 9:00

    # Busy intervals for each person (in minutes from 9:00)
    schedules = {
        "Andrea": ["9:30-10:30", "13:30-14:30"],
        "Ruth": ["12:30-13:00", "15:00-15:30"],
        "Steven": ["10:00-10:30", "11:00-11:30", "12:00-12:30", "13:30-14:00", "15:00-16:00"],
        "Grace": [],
        "Kyle": ["9:00-9:30", "10:30-12:00", "12:30-13:00", "13:30-15:00", "15:30-16:00", "16:30-17:00"],
        "Elijah": ["9:00-11:00", "11:30-13:00", "13:30-14:00", "15:30-16:00", "16:30-17:00"],
        "Lori": ["9:00-9:30", "10:00-11:30", "12:00-13:30", "14:00-16:00", "16:30-17:00"]
    }

    # Collect all busy intervals
    busy_intervals = []
    for person, blocks in schedules.items():
        for block in blocks:
            start_str, end_str = block.split('-')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            busy_intervals.append((start_min, end_min))

    # Sort intervals by start time
    busy_intervals.sort()

    # Merge overlapping busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged or merged[-1][1] < start:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)

    # Find free intervals within work hours
    free_intervals = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))

    # Look for first free interval of at least 30 minutes
    meeting_duration = 30
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            # Found slot
            meeting_start = start
            meeting_end = start + meeting_duration
            print(f"{minutes_to_time(meeting_start)}-{minutes_to_time(meeting_end)}")
            print("Monday")
            return

    print("No suitable slot found")

if __name__ == "__main__":
    main()