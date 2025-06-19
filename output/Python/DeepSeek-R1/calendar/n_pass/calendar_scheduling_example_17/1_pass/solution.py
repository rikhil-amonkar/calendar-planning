def main():
    # Convert time string to minutes since 00:00 for easier calculations, then adjust relative to 9:00
    def to_minutes(time_str):
        h, m = time_str.split(':')
        return int(h) * 60 + int(m)
    
    work_start_min = to_minutes('9:00')  # 540 minutes (from 00:00)
    work_end_min = to_minutes('17:00')   # 1020 minutes (from 00:00)
    
    # Adjust to minutes relative to 9:00 (so 9:00 becomes 0)
    def adjust(minutes):
        return minutes - work_start_min
    
    # Convert minutes (relative to 9:00) back to absolute time string
    def to_time_str(minutes):
        total_minutes = work_start_min + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"
    
    # Define busy intervals for each participant (in absolute times)
    margaret_busy = [
        ("9:00", "10:00"),
        ("10:30", "11:00"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("15:00", "15:30")
    ]
    
    donna_busy = [
        ("14:30", "15:00"),
        ("16:00", "16:30")
    ]
    
    helen_busy = [
        ("9:00", "9:30"),
        ("10:00", "11:30"),
        ("13:00", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "17:00"),
        ("13:30", "17:00")   # Additional constraint: Helen not available after 13:30
    ]
    
    # Convert all busy intervals to adjusted minutes (relative to 9:00)
    all_busy = []
    for start, end in margaret_busy:
        s = adjust(to_minutes(start))
        e = adjust(to_minutes(end))
        all_busy.append((s, e))
    
    for start, end in donna_busy:
        s = adjust(to_minutes(start))
        e = adjust(to_minutes(end))
        all_busy.append((s, e))
    
    for start, end in helen_busy:
        s = adjust(to_minutes(start))
        e = adjust(to_minutes(end))
        all_busy.append((s, e))
    
    # Sort intervals by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    current_start, current_end = all_busy[0]
    for s, e in all_busy[1:]:
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    
    # Find free intervals within working hours (0 to 480 minutes relative to 9:00)
    free_intervals = []
    last_end = 0
    for start, end in merged:
        if start > last_end:
            free_intervals.append((last_end, start))
        last_end = end
    if last_end < 480:
        free_intervals.append((last_end, 480))
    
    # Find the first free interval that can accommodate 30 minutes and starts by 13:30 (270 minutes)
    meeting_start = None
    for start, end in free_intervals:
        duration_needed = 30
        # Check if the interval is long enough
        if end - start >= duration_needed:
            # The meeting must start by 13:30 (270 minutes)
            latest_start = min(end - duration_needed, 270)
            if start <= latest_start:
                meeting_start = start
                break
    
    if meeting_start is None:
        print("No suitable time found")
    else:
        meeting_end = meeting_start + 30
        # Convert to absolute time strings
        start_time_abs = to_time_str(meeting_start)
        end_time_abs = to_time_str(meeting_end)
        # Format as HH:MM:HH:MM
        time_range_str = f"{start_time_abs[:5].replace(':', '')}:{end_time_abs[:5].replace(':', '')}"
        # Output day and time range
        print("Monday")
        print(time_range_str)

if __name__ == "__main__":
    main()