def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # All busy intervals in minutes (start, end)
    busy_intervals = [
        # Gregory
        (540, 570), (690, 720),
        # Jonathan
        (540, 570), (720, 750), (780, 810), (900, 960), (990, 1020),
        # Barbara
        (600, 630), (810, 840),
        # Jesse
        (600, 660), (750, 870),
        # Alan
        (570, 660), (690, 750), (780, 930), (960, 1020),
        # Nicole
        (540, 630), (690, 720), (750, 810), (840, 1020),
        # Catherine
        (540, 630), (720, 810), (900, 930), (960, 990)
    ]
    
    # Sort busy intervals by start time
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged = []
    if sorted_busy:
        current_start, current_end = sorted_busy[0]
        for s, e in sorted_busy[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Calculate free intervals within work hours
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
        if current >= work_end:
            break
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Find the first free interval that fits the meeting duration
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    else:
        # According to the problem, a solution exists, so this should not happen
        meeting_start = None
        meeting_end = None
    
    # Convert meeting time to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_hour = meeting_start // 60
    start_min = meeting_start % 60
    end_hour = meeting_end // 60
    end_min = meeting_end % 60
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    
    print(f"Monday {{{time_str}}}")

if __name__ == "__main__":
    main()