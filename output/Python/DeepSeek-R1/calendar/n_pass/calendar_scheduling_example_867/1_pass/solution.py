def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    mins = minutes_val % 60
    return f"{hours}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        s, e = sorted_intervals[i]
        if s <= end:
            end = max(end, e)
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    return merged

def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    merged_busy = merge_intervals(busy_intervals)
    free = []
    current = work_start
    for start_busy, end_busy in merged_busy:
        if current < start_busy:
            free.append((current, start_busy))
        current = max(current, end_busy)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_common_free_intervals(free1, free2):
    common = []
    i = j = 0
    while i < len(free1) and j < len(free2):
        start1, end1 = free1[i]
        start2, end2 = free2[j]
        low = max(start1, start2)
        high = min(end1, end2)
        if low < high:
            common.append((low, high))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return common

def main():
    # Define busy intervals as strings for each day and participant
    busy = {
        'Wednesday': {
            'Betty': [('9:30', '10:30'), ('13:00', '13:30'), ('14:00', '14:30')],
            'Scott': [('9:30', '12:30'), ('13:00', '13:30'), ('14:00', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')]
        },
        'Thursday': {
            'Betty': [('15:00', '15:30'), ('16:30', '17:00')],
            'Scott': [('15:00', '16:00'), ('16:30', '17:00')]
        }
    }
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    # For Thursday, we adjust work hours to 15:00-17:00 (900-1020 minutes) due to Betty's constraint
    days_order = ['Thursday', 'Wednesday']
    work_hours = {
        'Wednesday': (9*60, 17*60),   # 540, 1020
        'Thursday': (15*60, 17*60)     # 900, 1020
    }
    
    meeting_duration = 30  # minutes
    result_day = None
    meeting_interval = None
    
    for day in days_order:
        work_start, work_end = work_hours[day]
        
        # Convert busy intervals to minutes for Betty and Scott
        busy_betty = []
        for interval in busy[day]['Betty']:
            s, e = interval
            busy_betty.append((time_to_minutes(s), time_to_minutes(e)))
        
        busy_scott = []
        for interval in busy[day]['Scott']:
            s, e = interval
            busy_scott.append((time_to_minutes(s), time_to_minutes(e)))
        
        # Get free intervals
        free_betty = get_free_intervals(busy_betty, work_start, work_end)
        free_scott = get_free_intervals(busy_scott, work_start, work_end)
        
        # Find common free intervals
        common = find_common_free_intervals(free_betty, free_scott)
        
        # Check for a slot of at least 30 minutes
        for interval in common:
            start, end = interval
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                result_day = day
                meeting_interval = (meeting_start, meeting_end)
                break
        
        if result_day:
            break
    
    # Output the result
    if result_day:
        start_min, end_min = meeting_interval
        start_str = minutes_to_time(start_min)
        end_str = minutes_to_time(end_min)
        time_range_str = f"{start_str}:{end_str}"
        print(result_day)
        print("{" + time_range_str + "}")
    else:
        # According to the problem, there is a solution, so this should not happen
        print("No suitable time found")

if __name__ == "__main__":
    main()