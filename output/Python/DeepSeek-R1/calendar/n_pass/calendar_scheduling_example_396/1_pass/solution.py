def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])

    # Work hours boundaries
    work_start = time_to_minutes("9:00")  # 540 minutes
    work_end = time_to_minutes("17:00")   # 1020 minutes
    meeting_duration = 30  # minutes

    # Collect all busy intervals (in minutes)
    busy_intervals = []
    
    # Andrea: no meetings (skip)
    
    # Jack's meetings
    busy_intervals.append([time_to_minutes("9:00"), time_to_minutes("9:30")])
    busy_intervals.append([time_to_minutes("14:00"), time_to_minutes("14:30")])
    
    # Madison's meetings
    busy_intervals.append([time_to_minutes("9:30"), time_to_minutes("10:30")])
    busy_intervals.append([time_to_minutes("13:00"), time_to_minutes("14:00")])
    busy_intervals.append([time_to_minutes("15:00"), time_to_minutes("15:30")])
    busy_intervals.append([time_to_minutes("16:30"), time_to_minutes("17:00")])
    
    # Rachel's meetings
    busy_intervals.append([time_to_minutes("9:30"), time_to_minutes("10:30")])
    busy_intervals.append([time_to_minutes("11:00"), time_to_minutes("11:30")])
    busy_intervals.append([time_to_minutes("12:00"), time_to_minutes("13:30")])
    busy_intervals.append([time_to_minutes("14:30"), time_to_minutes("15:30")])
    busy_intervals.append([time_to_minutes("16:00"), time_to_minutes("17:00")])
    
    # Douglas's meetings
    busy_intervals.append([time_to_minutes("9:00"), time_to_minutes("11:30")])
    busy_intervals.append([time_to_minutes("12:00"), time_to_minutes("16:30")])
    
    # Ryan's meetings
    busy_intervals.append([time_to_minutes("9:00"), time_to_minutes("9:30")])
    busy_intervals.append([time_to_minutes("13:00"), time_to_minutes("14:00")])
    busy_intervals.append([time_to_minutes("14:30"), time_to_minutes("17:00")])
    
    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping busy intervals
    merged_busy = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged_busy.append([current_start, current_end])
                current_start, current_end = interval
        merged_busy.append([current_start, current_end])
    
    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for start, end in merged_busy:
        if current < start:
            free_intervals.append([current, start])
        current = max(current, end)
    if current < work_end:
        free_intervals.append([current, work_end])
    
    # Find the first free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        print("No solution found")
        return
    
    meeting_end = meeting_start + meeting_duration
    
    # Format meeting times
    def format_time(minutes):
        return f"{minutes // 60:02d}:{minutes % 60:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    time_range_str = f"{start_str}:{end_str}"
    
    # Output day and time range
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()