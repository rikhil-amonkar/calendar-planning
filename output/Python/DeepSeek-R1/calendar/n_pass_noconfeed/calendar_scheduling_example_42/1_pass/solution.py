def main():
    # Work hours: 9:00 to 17:00 (480 minutes)
    day_start = 9 * 60  # 9:00 in minutes since midnight
    day_end = 17 * 60   # 17:00 in minutes since midnight
    duration = 60        # 1 hour meeting

    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    # Busy intervals for each participant (in minutes since midnight)
    julie_busy = [
        ("9:00", "9:30"), ("11:00", "11:30"), ("12:00", "12:30"), 
        ("13:30", "14:00"), ("16:00", "17:00")
    ]
    sean_busy = [
        ("9:00", "9:30"), ("13:00", "13:30"), ("15:00", "15:30"), 
        ("16:00", "16:30")
    ]
    lori_busy = [
        ("10:00", "10:30"), ("11:00", "13:00"), ("15:30", "17:00")
    ]

    # Combine all busy intervals
    all_busy = []
    for start, end in julie_busy:
        all_busy.append((time_to_minutes(start), time_to_minutes(end)))
    for start, end in sean_busy:
        all_busy.append((time_to_minutes(start), time_to_minutes(end)))
    for start, end in lori_busy:
        all_busy.append((time_to_minutes(start), time_to_minutes(end)))

    # Merge overlapping busy intervals
    all_busy.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = all_busy[0]
    for s, e in all_busy[1:]:
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))

    # Find free intervals
    free_intervals = []
    # Before first busy interval
    if day_start < merged[0][0]:
        free_intervals.append((day_start, merged[0][0]))
    # Between busy intervals
    for i in range(1, len(merged)):
        prev_end = merged[i-1][1]
        curr_start = merged[i][0]
        if prev_end < curr_start:
            free_intervals.append((prev_end, curr_start))
    # After last busy interval
    if merged[-1][1] < day_end:
        free_intervals.append((merged[-1][1], day_end))

    # Find first free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            break

    # Convert meeting start and end to time strings
    def minutes_to_time(mins):
        hour = mins // 60
        minute = mins % 60
        return f"{hour:02d}:{minute:02d}"

    meeting_end = meeting_start + duration
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # Output the day and time range
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()