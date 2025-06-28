def main():
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    meeting_duration = 30
    
    # Busy intervals in minutes (start, end) for each participant
    busy_intervals = [
        # Patrick
        (540, 570), (600, 630), (810, 840), (960, 990),
        # Kayla
        (750, 810), (900, 930), (960, 990),
        # Carl
        (630, 660), (720, 750), (780, 810), (870, 1020),
        # Christian
        (540, 750), (780, 840), (870, 1020)
    ]
    
    # Sort busy intervals by start time
    sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if sorted_intervals:
        current_start, current_end = sorted_intervals[0]
        for interval in sorted_intervals[1:]:
            s, e = interval
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
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
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    
    # Convert meeting start and end to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    
    # Output the meeting time and day
    print(f"{start_str}:{end_str}")
    print("Monday")

if __name__ == "__main__":
    main()