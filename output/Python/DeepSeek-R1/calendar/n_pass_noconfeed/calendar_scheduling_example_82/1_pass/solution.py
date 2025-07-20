def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time_str(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Work hours: 9:00 to 17:00
    work_start = time_str_to_minutes("9:00")  # 540 minutes
    work_end = time_str_to_minutes("17:00")   # 1020 minutes
    
    # Busy intervals for each participant in minutes
    michael_busy = [
        ("9:30", "10:30"),
        ("15:00", "15:30"),
        ("16:00", "16:30")
    ]
    eric_busy = []  # Eric has no meetings
    arthur_busy = [
        ("9:00", "12:00"),
        ("13:00", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
    
    # Convert all busy intervals to minutes and collect
    busy_intervals = []
    for start, end in michael_busy:
        busy_intervals.append((time_str_to_minutes(start), time_str_to_minutes(end)))
    for start, end in eric_busy:
        busy_intervals.append((time_str_to_minutes(start), time_str_to_minutes(end)))
    for start, end in arthur_busy:
        busy_intervals.append((time_str_to_minutes(start), time_str_to_minutes(end)))
    
    # Sort by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge busy intervals
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
    
    # Find free intervals within work hours
    free_intervals = []
    start_boundary = work_start
    
    for busy_start, busy_end in merged:
        if start_boundary < busy_start:
            free_intervals.append((start_boundary, busy_start))
        start_boundary = busy_end
    
    if start_boundary < work_end:
        free_intervals.append((start_boundary, work_end))
    
    # Find the first free interval that can fit the meeting
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            # Convert back to time strings
            start_str = minutes_to_time_str(meeting_start)
            end_str = minutes_to_time_str(meeting_end)
            time_range_str = f"{start_str}:{end_str}"
            print("Monday")
            print(time_range_str)
            return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()