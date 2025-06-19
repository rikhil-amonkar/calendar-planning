def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # List of busy intervals (start_minute, end_minute) for all participants
    busy_intervals = []
    
    # Judy's busy times
    busy_intervals.append((13 * 60, 13 * 60 + 30))  # 13:00-13:30
    busy_intervals.append((16 * 60, 16 * 60 + 30))  # 16:00-16:30
    
    # Olivia's busy times
    busy_intervals.append((10 * 60, 10 * 60 + 30))  # 10:00-10:30
    busy_intervals.append((12 * 60, 13 * 60))        # 12:00-13:00
    busy_intervals.append((14 * 60, 14 * 60 + 30))   # 14:00-14:30
    
    # Eric: free all day (no busy intervals)
    
    # Jacqueline's busy times
    busy_intervals.append((10 * 60, 10 * 60 + 30))  # 10:00-10:30
    busy_intervals.append((15 * 60, 15 * 60 + 30))  # 15:00-15:30
    
    # Laura's busy times
    busy_intervals.append((9 * 60, 10 * 60))         # 9:00-10:00
    busy_intervals.append((10 * 60 + 30, 12 * 60))   # 10:30-12:00
    busy_intervals.append((13 * 60, 13 * 60 + 30))   # 13:00-13:30
    busy_intervals.append((14 * 60 + 30, 15 * 60))   # 14:30-15:00
    busy_intervals.append((15 * 60 + 30, 17 * 60))   # 15:30-17:00
    
    # Tyler's busy times
    busy_intervals.append((9 * 60, 10 * 60))         # 9:00-10:00
    busy_intervals.append((11 * 60, 11 * 60 + 30))   # 11:00-11:30
    busy_intervals.append((12 * 60 + 30, 13 * 60))   # 12:30-13:00
    busy_intervals.append((14 * 60, 14 * 60 + 30))   # 14:00-14:30
    busy_intervals.append((15 * 60 + 30, 17 * 60))   # 15:30-17:00
    
    # Lisa's busy times
    busy_intervals.append((9 * 60 + 30, 10 * 60 + 30))  # 9:30-10:30
    busy_intervals.append((11 * 60, 11 * 60 + 30))      # 11:00-11:30
    busy_intervals.append((12 * 60, 12 * 60 + 30))      # 12:00-12:30
    busy_intervals.append((13 * 60, 13 * 60 + 30))      # 13:00-13:30
    busy_intervals.append((14 * 60, 14 * 60 + 30))      # 14:00-14:30
    busy_intervals.append((16 * 60, 17 * 60))           # 16:00-17:00

    # Merge overlapping busy intervals
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    start, end = busy_intervals[0]
    for interval in busy_intervals[1:]:
        if interval[0] <= end:
            end = max(end, interval[1])
        else:
            merged.append((start, end))
            start, end = interval
    merged.append((start, end))

    # Compute free intervals within work hours
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = end
    if current < work_end:
        free_intervals.append((current, work_end))

    # Find first free interval with sufficient duration
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break

    # Format the meeting time
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    time_output = f"{start_str}:{end_str}"

    # Output day and time
    print("Monday")
    print(time_output)

if __name__ == "__main__":
    main()