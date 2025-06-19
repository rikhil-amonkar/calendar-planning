def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes):
    total_minutes = minutes + 9 * 60
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Convert work hours to minutes
    work_start = time_to_minutes("09:00")  # 0 minutes
    work_end = time_to_minutes("17:00")    # 480 minutes
    
    # Collect all busy intervals in minutes
    busy_intervals = []
    
    # Michael's busy times
    michael_meetings = [
        ("09:30", "10:30"),
        ("15:00", "15:30"),
        ("16:00", "16:30")
    ]
    for start, end in michael_meetings:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        busy_intervals.append((s, e))
    
    # Eric has no meetings, so no intervals to add
    
    # Arthur's busy times
    arthur_meetings = [
        ("09:00", "12:00"),
        ("13:00", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
    for start, end in arthur_meetings:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        busy_intervals.append((s, e))
    
    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
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
    if not merged:
        free_intervals.append((work_start, work_end))
    else:
        # Before first meeting
        if merged[0][0] > work_start:
            free_intervals.append((work_start, merged[0][0]))
        # Between meetings
        for i in range(1, len(merged)):
            prev_end = merged[i-1][1]
            curr_start = merged[i][0]
            if curr_start > prev_end:
                free_intervals.append((prev_end, curr_start))
        # After last meeting
        if merged[-1][1] < work_end:
            free_intervals.append((merged[-1][1], work_end))
    
    # Find the first free slot of at least 30 minutes
    meeting_duration = 30
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            # Format as HH:MM:HH:MM and day
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            print(f"Monday:{start_str}:{end_str}")
            return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()