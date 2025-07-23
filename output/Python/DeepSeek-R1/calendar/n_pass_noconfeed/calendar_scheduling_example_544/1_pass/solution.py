def main():
    # Define the day
    day = "Monday"
    
    # Convert time to minutes since midnight
    work_start = 9 * 60  # 9:00
    # Albert cannot meet after 11:00, so the meeting must end by 11:00 (660 minutes)
    effective_end = 11 * 60  # 11:00
    meeting_duration = 30  # minutes
    
    # Albert's busy intervals in minutes (start inclusive, end exclusive)
    # Only consider intervals that overlap with [work_start, effective_end]
    busy_intervals = [
        (9 * 60, 10 * 60),     # 9:00-10:00
        (10 * 60 + 30, 12 * 60) # 10:30-12:00, but truncated at 11:00
    ]
    
    # Adjust the second busy interval to end at effective_end (11:00)
    adjusted_busy = []
    for start, end in busy_intervals:
        if start < effective_end:
            adj_end = min(end, effective_end)
            adjusted_busy.append((start, adj_end))
    busy_intervals = adjusted_busy
    
    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Find free intervals for Albert between work_start and effective_end
    free_intervals = []
    current = work_start
    
    for start, end in busy_intervals:
        if current < start:
            # Found a free interval from current to start
            free_intervals.append((current, start))
        current = max(current, end)
    
    # Check after the last busy interval
    if current < effective_end:
        free_intervals.append((current, effective_end))
    
    # Find the first free interval that can fit the meeting
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            break
    else:
        # According to the problem, a solution exists, so this should not happen
        meeting_start = None
        meeting_end = None
    
    # Convert meeting times to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    
    # Output day and time range in HH:MM:HH:MM format
    print(f"{day} {start_str}:{end_str}")

if __name__ == "__main__":
    main()