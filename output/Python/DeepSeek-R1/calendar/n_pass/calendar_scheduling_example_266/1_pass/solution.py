def main():
    # Meeting duration in minutes
    duration = 30
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    day = "Monday"
    
    # Collect all busy intervals in minutes since midnight
    busy_intervals = []
    
    # Joe's schedule
    busy_intervals.append((9*60 + 30, 10*60))      # 9:30-10:00
    busy_intervals.append((10*60 + 30, 11*60))     # 10:30-11:00
    
    # Keith's schedule
    busy_intervals.append((11*60 + 30, 12*60))     # 11:30-12:00
    busy_intervals.append((15*60, 15*60 + 30))      # 15:00-15:30
    
    # Patricia's schedule
    busy_intervals.append((9*60, 9*60 + 30))        # 9:00-9:30
    busy_intervals.append((13*60, 13*60 + 30))      # 13:00-13:30
    
    # Nancy's schedule
    busy_intervals.append((9*60, 11*60))            # 9:00-11:00
    busy_intervals.append((11*60 + 30, 16*60 + 30)) # 11:30-16:30
    
    # Pamela's schedule
    busy_intervals.append((9*60, 10*60))            # 9:00-10:00
    busy_intervals.append((10*60 + 30, 11*60))      # 10:30-11:00
    busy_intervals.append((11*60 + 30, 12*60 + 30)) # 11:30-12:30
    busy_intervals.append((13*60, 14*60))           # 13:00-14:00
    busy_intervals.append((14*60 + 30, 15*60))      # 14:30-15:00
    busy_intervals.append((15*60 + 30, 16*60))      # 15:30-16:00
    busy_intervals.append((16*60 + 30, 17*60))      # 16:30-17:00

    # Merge overlapping or adjacent busy intervals
    if not busy_intervals:
        merged = []
    else:
        sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
        merged = []
        start, end = sorted_intervals[0]
        for i in range(1, len(sorted_intervals)):
            s, e = sorted_intervals[i]
            if s <= end:  # Overlapping or adjacent
                end = max(end, e)
            else:
                merged.append((start, end))
                start, end = s, e
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
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            break
    
    # Format the meeting time
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    time_range = f"{start_str}:{end_str}"
    
    # Output day and time range
    print(day)
    print(time_range)

if __name__ == "__main__":
    main()