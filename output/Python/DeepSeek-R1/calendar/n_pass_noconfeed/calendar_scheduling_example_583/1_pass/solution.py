def main():
    # Convert time to minutes since midnight
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00
    meeting_duration = 30  # minutes

    # Busy intervals in minutes: (start, end)
    lisa_busy = [
        (9*60, 9*60+30),   # 9:00-9:30
        (10*60+30, 11*60), # 10:30-11:00
        (14*60, 16*60)     # 14:00-16:00
    ]
    anthony_busy = [
        (9*60, 9*60+30),       # 9:00-9:30
        (11*60, 11*60+30),     # 11:00-11:30
        (12*60+30, 13*60+30),  # 12:30-13:30
        (14*60, 15*60),        # 14:00-15:00
        (15*60+30, 16*60),     # 15:30-16:00
        (16*60+30, 17*60)      # 16:30-17:00
    ]

    # Combine and sort busy intervals
    busy_list = lisa_busy + anthony_busy
    busy_list.sort()

    # Merge overlapping intervals
    merged = []
    for start, end in busy_list:
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
    # Before first busy interval
    if work_start < merged[0][0]:
        free_intervals.append((work_start, merged[0][0]))
    # Between busy intervals
    for i in range(len(merged) - 1):
        gap_start = merged[i][1]
        gap_end = merged[i+1][0]
        if gap_start < gap_end:
            free_intervals.append((gap_start, gap_end))
    # After last busy interval
    if merged[-1][1] < work_end:
        free_intervals.append((merged[-1][1], work_end))

    # Find earliest free interval of sufficient length
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            break

    # Format meeting time as HH:MM
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    time_range_str = f"{start_str}:{end_str}"

    # Output results
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()