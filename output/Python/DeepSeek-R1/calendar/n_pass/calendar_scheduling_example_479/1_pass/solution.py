def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Work hours
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    
    # Participants' busy intervals (each as list of [start, end] in minutes)
    busy_intervals = []
    
    # Evelyn: free entire day -> no intervals
    # Joshua
    busy_intervals.extend([
        [time_to_minutes("11:00"), time_to_minutes("12:30")],
        [time_to_minutes("13:30"), time_to_minutes("14:30")],
        [time_to_minutes("16:30"), time_to_minutes("17:00")]
    ])
    
    # Kevin: free entire day -> no intervals
    # Gerald: free entire day -> no intervals
    
    # Jerry
    busy_intervals.extend([
        [time_to_minutes("9:00"), time_to_minutes("9:30")],
        [time_to_minutes("10:30"), time_to_minutes("12:00")],
        [time_to_minutes("12:30"), time_to_minutes("13:00")],
        [time_to_minutes("13:30"), time_to_minutes("14:00")],
        [time_to_minutes("14:30"), time_to_minutes("15:00")],
        [time_to_minutes("15:30"), time_to_minutes("16:00")]
    ])
    
    # Jesse
    busy_intervals.extend([
        [time_to_minutes("9:00"), time_to_minutes("9:30")],
        [time_to_minutes("10:30"), time_to_minutes("12:00")],
        [time_to_minutes("12:30"), time_to_minutes("13:00")],
        [time_to_minutes("14:30"), time_to_minutes("15:00")],
        [time_to_minutes("15:30"), time_to_minutes("16:30")]
    ])
    
    # Kenneth
    busy_intervals.extend([
        [time_to_minutes("10:30"), time_to_minutes("12:30")],
        [time_to_minutes("13:30"), time_to_minutes("14:00")],
        [time_to_minutes("14:30"), time_to_minutes("15:00")],
        [time_to_minutes("15:30"), time_to_minutes("16:00")],
        [time_to_minutes("16:30"), time_to_minutes("17:00")]
    ])
    
    # Sort all busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append([current_start, current_end])
                current_start, current_end = interval
        merged.append([current_start, current_end])
    
    # Find free intervals within work hours
    free_intervals = []
    start = work_start
    
    for interval in merged:
        if interval[0] > start:
            free_intervals.append([start, interval[0]])
        start = max(start, interval[1])
    if start < work_end:
        free_intervals.append([start, work_end])
    
    # Find the first free interval that is at least 60 minutes
    meeting_duration = 60
    for interval in free_intervals:
        start_min, end_min = interval
        if end_min - start_min >= meeting_duration:
            # Found a suitable interval
            meeting_start = start_min
            meeting_end = start_min + meeting_duration
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            print("Monday")
            print(f"{start_str}:{end_str}")
            return
    
    # If no suitable interval found (though problem states there is one)
    print("No suitable time found")

if __name__ == "__main__":
    main()