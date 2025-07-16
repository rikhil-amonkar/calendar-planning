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

def compute_free(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    for interval in busy_intervals:
        s, e = interval
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        low = max(s1, s2)
        high = min(e1, e2)
        if low < high:
            common.append((low, high))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return common

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    work_start = 540
    work_end = 1020
    days_order = ['Monday', 'Wednesday', 'Tuesday']
    
    for day in days_order:
        susan_busy = []
        sandra_busy = []
        
        if day == 'Monday':
            susan_busy = [(750, 780), (810, 840)]
            sandra_busy = [(540, 780), (840, 900), (960, 990), (960, 1020)]
        elif day == 'Tuesday':
            susan_busy = [(690, 720)]
            sandra_busy = [(540, 570), (630, 720), (750, 810), (840, 870), (960, 1020)]
        elif day == 'Wednesday':
            susan_busy = [(570, 630), (840, 870), (930, 990)]
            sandra_busy = [(540, 690), (720, 750), (780, 1020)]
        
        susan_busy_merged = merge_intervals(susan_busy)
        sandra_busy_merged = merge_intervals(sandra_busy)
        
        susan_free = compute_free(susan_busy_merged, work_start, work_end)
        sandra_free = compute_free(sandra_busy_merged, work_start, work_end)
        
        common_free = intersect_intervals(susan_free, sandra_free)
        
        for (start_min, end_min) in common_free:
            duration = end_min - start_min
            if duration >= 30:
                meeting_start = start_min
                meeting_end = start_min + 30
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                time_str = f"{start_str}:{end_str}"
                print(day)
                print(time_str)
                return
                
    print("No suitable time found.")

if __name__ == "__main__":
    main()