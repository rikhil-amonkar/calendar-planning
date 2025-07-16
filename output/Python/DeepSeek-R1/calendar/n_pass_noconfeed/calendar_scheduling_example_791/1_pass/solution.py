def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Wednesday only (since Mon/Tue are blocked for Ruth)
    day = "Wednesday"
    
    # Nicole's busy times on Wednesday (converted to minutes)
    nicole_busy = [
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
    
    # Ruth's busy times on Wednesday (converted to minutes)
    # Also, Ruth doesn't want to meet after 13:30, so set work_end_ruth to 13:30 (810 minutes)
    work_end_ruth = time_to_minutes("13:30")
    ruth_busy = [
        (time_to_minutes("09:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30"))
    ]
    
    # Function to calculate free intervals given work start, work end, and busy intervals
    def get_free_intervals(work_start, work_end, busy_intervals):
        if not busy_intervals:
            return [(work_start, work_end)]
        # Sort busy intervals by start time
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free_intervals = []
        current_start = work_start
        
        for start, end in sorted_busy:
            if current_start < start:
                free_intervals.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < work_end:
            free_intervals.append((current_start, work_end))
        return free_intervals

    # Get free intervals for Nicole (entire work day) and Ruth (only until 13:30)
    nicole_free = get_free_intervals(work_start, work_end, nicole_busy)
    ruth_free = get_free_intervals(work_start, work_end_ruth, ruth_busy)
    
    # Find overlapping free intervals between Nicole and Ruth
    overlapping = []
    for n_start, n_end in nicole_free:
        for r_start, r_end in ruth_free:
            low = max(n_start, r_start)
            high = min(n_end, r_end)
            if low < high:  # There is an overlap
                overlapping.append((low, high))
    
    # Find the first overlapping interval that can fit a 30-minute meeting
    meeting_start = None
    for start, end in overlapping:
        if end - start >= 30:  # At least 30 minutes available
            meeting_start = start
            break
    
    if meeting_start is None:
        # According to the problem, there is a solution, so this should not happen
        print("No suitable time found")
        return
    
    meeting_end = meeting_start + 30
    
    # Convert to time strings
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # Output day and time range in HH:MM:HH:MM format
    print(day)
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()