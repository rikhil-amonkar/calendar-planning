def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        if sorted_intervals[i][0] <= end:
            end = max(end, sorted_intervals[i][1])
        else:
            merged.append((start, end))
            start, end = sorted_intervals[i]
    merged.append((start, end))
    return merged

def free_intervals(busy_intervals, work_start, work_end):
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

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            result.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    day_index_map = {
        'Monday': 0,
        'Tuesday': 1,
        'Wednesday': 2,
        'Thursday': 3,
        'Friday': 4
    }
    
    # Terry's busy times
    terry_busy = {
        'Monday': [('10:30','11:00'), ('12:30','14:00'), ('15:00','17:00')],
        'Tuesday': [('9:30','10:00'), ('10:30','11:00'), ('14:00','14:30'), ('16:00','16:30')],
        'Wednesday': [('9:30','10:30'), ('11:00','12:00'), ('13:00','13:30'), ('15:00','16:00'), ('16:30','17:00')],
        'Thursday': [('9:30','10:00'), ('12:00','12:30'), ('13:00','14:30'), ('16:00','16:30')],
        'Friday': [('9:00','11:30'), ('12:00','12:30'), ('13:30','16:00'), ('16:30','17:00')]
    }
    
    # Frances's busy times
    frances_busy = {
        'Monday': [('9:30','11:00'), ('11:30','13:00'), ('14:00','14:30'), ('15:00','16:00')],
        'Tuesday': [('9:00','9:30'), ('10:00','10:30'), ('11:00','12:00'), ('13:00','14:30'), ('15:30','16:30')],
        'Wednesday': [('9:30','10:00'), ('10:30','11:00'), ('11:30','16:00'), ('16:30','17:00')],
        'Thursday': [('11:00','12:30'), ('14:30','17:00')],
        'Friday': [('9:30','10:30'), ('11:00','12:30'), ('13:00','16:00'), ('16:30','17:00')]
    }
    
    non_tuesday_candidates = []
    tuesday_candidates = []
    
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
        # Convert Terry's busy times to minutes
        terry_busy_minutes = []
        for interval in terry_busy[day]:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            terry_busy_minutes.append((start_min, end_min))
        
        # Convert Frances's busy times to minutes
        frances_busy_minutes = []
        for interval in frances_busy[day]:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            frances_busy_minutes.append((start_min, end_min))
        
        # Get free intervals for Terry and Frances
        terry_free = free_intervals(terry_busy_minutes, work_start, work_end)
        frances_free = free_intervals(frances_busy_minutes, work_start, work_end)
        
        # Find overlapping free intervals
        overlap = intersect_intervals(terry_free, frances_free)
        
        # Check each overlapping interval for 30-minute availability
        for start, end in overlap:
            duration = end - start
            if duration >= 30:
                day_idx = day_index_map[day]
                candidate = (day_idx, start, day)
                if day != 'Tuesday':
                    non_tuesday_candidates.append(candidate)
                else:
                    tuesday_candidates.append(candidate)
    
    # Select the earliest candidate, avoiding Tuesday if possible
    if non_tuesday_candidates:
        non_tuesday_candidates.sort(key=lambda x: (x[0], x[1]))
        chosen = non_tuesday_candidates[0]
    elif tuesday_candidates:
        tuesday_candidates.sort(key=lambda x: (x[0], x[1]))
        chosen = tuesday_candidates[0]
    else:
        # According to the problem, a solution exists, so this should not happen
        print("No solution found")
        return
    
    day_name = chosen[2]
    start_minutes = chosen[1]
    end_minutes = start_minutes + 30
    start_str = minutes_to_time(start_minutes)
    end_str = minutes_to_time(end_minutes)
    time_range_str = f"{start_str}:{end_str}"
    
    print(day_name)
    print(time_range_str)

if __name__ == "__main__":
    main()