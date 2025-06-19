def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Given constraints and schedules
    day = "Monday"  # Only Monday is feasible due to John's constraints
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("14:30")  # John available until 14:30
    
    # Jennifer's busy intervals on Monday (converted to minutes and clipped to work_end)
    busy_intervals = [
        ("09:00", "11:00"),
        ("11:30", "13:00"),
        ("13:30", "14:30"),
        ("15:00", "17:00")
    ]
    busy_minutes = []
    for s, e in busy_intervals:
        s_min = time_to_minutes(s)
        e_min = time_to_minutes(e)
        if s_min < work_end:  # Only consider intervals starting before work_end
            e_min = min(e_min, work_end)
            busy_minutes.append((s_min, e_min))
    
    # Sort by start time
    busy_minutes.sort(key=lambda x: x[0])
    
    # Compute free intervals within work hours
    free_intervals = []
    current = work_start
    for s, e in busy_minutes:
        if s > current:
            gap_duration = s - current
            if gap_duration >= 30:  # Minimum meeting duration
                free_intervals.append((current, s))
        current = max(current, e)
    if work_end - current >= 30:
        free_intervals.append((current, work_end))
    
    # Select the first available free interval
    if free_intervals:
        start_min, end_min = free_intervals[0]
        meeting_end_min = start_min + 30  # Schedule first 30 minutes of the gap
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(meeting_end_min)
        print(day)
        print(f"{start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()