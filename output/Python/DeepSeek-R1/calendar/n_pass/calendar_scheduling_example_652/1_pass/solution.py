def main():
    # Meeting duration in minutes
    meeting_duration = 30
    
    # Work hours: 9:00 to 17:00 (in minutes from start of day)
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    
    # Lawrence constraint: cannot meet after 16:30 on Tuesday (990 minutes)
    lawrence_end_tuesday = 16 * 60 + 30  # 990 minutes (16:30)
    
    # Jesse's busy intervals on Tuesday (each as (start, end) in minutes)
    jesse_busy_tuesday = [
        (540, 570),   # 9:00-9:30
        (780, 810),   # 13:00-13:30
        (840, 900)    # 14:00-15:00
    ]
    
    # Lawrence's busy intervals on Tuesday
    lawrence_busy_tuesday = [
        (570, 630),   # 9:30-10:30
        (690, 750),   # 11:30-12:30
        (780, 810),   # 13:00-13:30
        (870, 900),   # 14:30-15:00
        (930, 990)    # 15:30-16:30
    ]
    
    # Calculate free intervals for Jesse on Tuesday within work hours
    jesse_free = calculate_free_intervals(work_start, work_end, jesse_busy_tuesday)
    
    # Calculate free intervals for Lawrence on Tuesday within [work_start, lawrence_end_tuesday]
    lawrence_free = calculate_free_intervals(work_start, lawrence_end_tuesday, lawrence_busy_tuesday)
    
    # Find overlapping free intervals
    overlapping = find_overlapping_intervals(jesse_free, lawrence_free)
    
    # Find the first overlapping interval that can fit the meeting
    meeting_start = None
    for start, end in overlapping:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        # According to the problem, a solution exists, so this should not happen
        print("No suitable time found")
        return
    
    meeting_end = meeting_start + meeting_duration
    
    # Convert meeting times to formatted strings
    start_hour = meeting_start // 60
    start_min = meeting_start % 60
    end_hour = meeting_end // 60
    end_min = meeting_end % 60
    
    # Format the time string as HH:MM:HH:MM within braces
    time_str = f"{{{start_hour}:{start_min:02d}:{end_hour}:{end_min:02d}}}"
    
    # Output the day and the time string
    print("Tuesday")
    print(time_str)

def calculate_free_intervals(start_bound, end_bound, busy_intervals):
    """Calculate free intervals within [start_bound, end_bound] given busy intervals."""
    # Sort busy intervals by start time
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = start_bound
    
    for b_start, b_end in busy_intervals:
        if current < b_start:
            # There is a free interval from current to b_start
            free.append((current, b_start))
        current = max(current, b_end)
    
    # Check for free interval after the last busy interval
    if current < end_bound:
        free.append((current, end_bound))
    
    return free

def find_overlapping_intervals(intervals1, intervals2):
    """Find overlapping intervals between two lists of intervals."""
    overlapping = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            low = max(start1, start2)
            high = min(end1, end2)
            if low < high:
                overlapping.append((low, high))
    # Sort by start time to get the earliest
    overlapping.sort(key=lambda x: x[0])
    return overlapping

if __name__ == "__main__":
    main()