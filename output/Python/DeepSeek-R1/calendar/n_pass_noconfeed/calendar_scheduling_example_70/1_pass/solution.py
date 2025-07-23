def main():
    # Work hours: 9:00 to 17:00 (represented as minutes from 9:00)
    work_start_min = 0
    work_end_min = 8 * 60  # 480 minutes (8 hours * 60 minutes)
    meeting_duration = 30  # minutes

    # Collect all busy intervals (start and end in minutes from 9:00)
    busy_intervals = []
    
    # Denise's busy times
    busy_intervals.append((180, 210))   # 12:00-12:30
    busy_intervals.append((390, 420))   # 15:30-16:00
    
    # Natalie's busy times
    busy_intervals.append((0, 150))     # 9:00-11:30
    busy_intervals.append((180, 240))   # 12:00-13:00
    busy_intervals.append((300, 330))   # 14:00-14:30
    busy_intervals.append((360, 480))   # 15:00-17:00
    
    # Angela has no meetings, so no intervals to add

    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged_busy = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    
    # Find free intervals within work hours
    free_intervals = []
    current = work_start_min
    for interval in merged_busy:
        s, e = interval
        if current < s:
            free_intervals.append((current, s))
        current = e
    if current < work_end_min:
        free_intervals.append((current, work_end_min))
    
    # Find earliest free interval that can accommodate the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        print("No suitable time found")
        return
    
    meeting_end = meeting_start + meeting_duration
    
    # Convert minutes to time strings (relative to 9:00)
    def minutes_to_time(minutes):
        hour = 9 + minutes // 60
        minute = minutes % 60
        return f"{hour}:{minute:02d}"
    
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # Output day and time range in the specified format
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()