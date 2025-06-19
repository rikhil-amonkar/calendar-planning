def compute_free_intervals(busy_intervals, window):
    start_min, end_min = window
    if not busy_intervals:
        return [(start_min, end_min)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = start_min
    for interval in sorted_busy:
        if interval[0] > current_start:
            free.append((current_start, interval[0]))
        if interval[1] > current_start:
            current_start = interval[1]
        if current_start >= end_min:
            break
    if current_start < end_min:
        free.append((current_start, end_min))
    return free

def intersect_intervals(intervals1, intervals2):
    result = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start_max = max(start1, start2)
            end_min = min(end1, end2)
            if start_max < end_min:
                result.append((start_max, end_min))
    return result

def main():
    anthony_busy = [(570, 600), (720, 780), (960, 990)]
    pamela_busy = [(570, 600), (990, 1020)]
    zachary_busy = [(540, 690), (720, 750), (780, 810), (870, 900), (960, 1020)]
    
    anthony_window = (540, 1020)
    pamela_window = (540, 870)
    zachary_window = (540, 1020)
    
    anthony_free = compute_free_intervals(anthony_busy, anthony_window)
    pamela_free = compute_free_intervals(pamela_busy, pamela_window)
    zachary_free = compute_free_intervals(zachary_busy, zachary_window)
    
    common_free = intersect_intervals(anthony_free, pamela_free)
    common_free = intersect_intervals(common_free, zachary_free)
    
    meeting_start = None
    meeting_end = None
    for start, end in common_free:
        if end - start >= 60:
            meeting_start = start
            meeting_end = start + 60
            break
    
    def format_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)
    time_range_str = f"{start_str}:{end_str}"
    
    print("Monday", time_range_str)

if __name__ == "__main__":
    main()