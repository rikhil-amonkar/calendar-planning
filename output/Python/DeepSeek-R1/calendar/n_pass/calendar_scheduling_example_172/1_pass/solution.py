def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes
    work_start = 0
    work_end = 480
    duration = 30

    # Busy intervals for each participant in minutes (relative to 9:00)
    patrick = [(0, 30), (60, 90), (270, 300), (420, 450)]
    kayla = [(210, 270), (360, 390), (420, 450)]
    carl = [(90, 120), (180, 210), (240, 270), (330, 480)]
    christian = [(0, 210), (240, 300), (330, 480)]
    
    # Combine all busy intervals
    busy_intervals = patrick + kayla + carl + christian
    
    # Sort by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
    
    # Find free intervals
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = end
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Find the first free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            break
    
    # If found, convert to time string
    if meeting_start is not None:
        meeting_end = meeting_start + duration
        start_hour = 9 + meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = 9 + meeting_end // 60
        end_minute = meeting_end % 60
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print("Monday")
        print(time_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()