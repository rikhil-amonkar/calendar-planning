def main():
    # Work hours: 9:00 to 17:00 (8 hours = 480 minutes)
    base_minutes = 9 * 60  # 540 minutes from midnight for 9:00
    duration = 30  # meeting duration in minutes
    work_end_relative = 8 * 60  # 480 minutes (17:00 - 9:00)
    
    # List to collect all busy intervals (in minutes relative to 9:00)
    busy_intervals = []
    
    # Helper function to convert time string to minutes relative to 9:00
    def time_str_to_relative_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        total_minutes = h * 60 + m
        return total_minutes - base_minutes
    
    # Judy: 13:00-13:30, 16:00-16:30
    intervals = ["13:00 to 13:30", "16:00 to 16:30"]
    for interval in intervals:
        start_str, end_str = interval.split(' to ')
        s = time_str_to_relative_minutes(start_str)
        e = time_str_to_relative_minutes(end_str)
        busy_intervals.append((s, e))
    
    # Olivia: 10:00-10:30, 12:00-13:00, 14:00-14:30
    intervals = ["10:00 to 10:30", "12:00 to 13:00", "14:00 to 14:30"]
    for interval in intervals:
        start_str, end_str = interval.split(' to ')
        s = time_str_to_relative_minutes(start_str)
        e = time_str_to_relative_minutes(end_str)
        busy_intervals.append((s, e))
    
    # Eric: free (no intervals)
    
    # Jacqueline: 10:00-10:30, 15:00-15:30
    intervals = ["10:00 to 10:30", "15:00 to 15:30"]
    for interval in intervals:
        start_str, end_str = interval.split(' to ')
        s = time_str_to_relative_minutes(start_str)
        e = time_str_to_relative_minutes(end_str)
        busy_intervals.append((s, e))
    
    # Laura: 9:00-10:00, 10:30-12:00, 13:00-13:30, 14:30-15:00, 15:30-17:00
    intervals = ["9:00 to 10:00", "10:30 to 12:00", "13:00 to 13:30", "14:30 to 15:00", "15:30 to 17:00"]
    for interval in intervals:
        start_str, end_str = interval.split(' to ')
        s = time_str_to_relative_minutes(start_str)
        e = time_str_to_relative_minutes(end_str)
        busy_intervals.append((s, e))
    
    # Tyler: 9:00-10:00, 11:00-11:30, 12:30-13:00, 14:00-14:30, 15:30-17:00
    intervals = ["9:00 to 10:00", "11:00 to 11:30", "12:30 to 13:00", "14:00 to 14:30", "15:30 to 17:00"]
    for interval in intervals:
        start_str, end_str = interval.split(' to ')
        s = time_str_to_relative_minutes(start_str)
        e = time_str_to_relative_minutes(end_str)
        busy_intervals.append((s, e))
    
    # Lisa: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 14:00-14:30, 16:00-17:00
    intervals = ["9:30 to 10:30", "11:00 to 11:30", "12:00 to 12:30", "13:00 to 13:30", "14:00 to 14:30", "16:00 to 17:00"]
    for interval in intervals:
        start_str, end_str = interval.split(' to ')
        s = time_str_to_relative_minutes(start_str)
        e = time_str_to_relative_minutes(end_str)
        busy_intervals.append((s, e))
    
    # Merge busy intervals
    if not busy_intervals:
        merged = []
    else:
        sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
        merged = []
        start_curr, end_curr = sorted_intervals[0]
        for s, e in sorted_intervals[1:]:
            if s <= end_curr:
                if e > end_curr:
                    end_curr = e
            else:
                merged.append((start_curr, end_curr))
                start_curr = s
                end_curr = e
        merged.append((start_curr, end_curr))
    
    # Find free intervals
    free_intervals = []
    prev_end = 0
    for s, e in merged:
        if s > prev_end:
            free_intervals.append((prev_end, s))
        prev_end = e
    if prev_end < work_end_relative:
        free_intervals.append((prev_end, work_end_relative))
    
    # Find first free interval with sufficient duration
    meeting_start = None
    for start_free, end_free in free_intervals:
        if end_free - start_free >= duration:
            meeting_start = start_free
            break
    
    if meeting_start is None:
        # According to the problem, there is a solution, so this should not happen
        print("Monday")
        print("00:00:00:00")  # fallback
        return
    
    meeting_end = meeting_start + duration
    
    # Convert meeting times to absolute time (HH:MM format)
    def minutes_to_time(minutes_relative):
        total_minutes_abs = base_minutes + minutes_relative
        h = total_minutes_abs // 60
        m = total_minutes_abs % 60
        return f"{h:02d}:{m:02d}"
    
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)
    
    # Output day and time range in HH:MM:HH:MM format
    print("Monday")
    print(f"{start_time_str}:{end_time_str}")

if __name__ == "__main__":
    main()