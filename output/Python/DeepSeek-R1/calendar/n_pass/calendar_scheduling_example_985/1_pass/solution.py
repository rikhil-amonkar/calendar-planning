def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        s, e = sorted_intervals[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    return merged

def compute_free_intervals(work_start, work_end, busy_intervals):
    merged_busy = merge_intervals(busy_intervals)
    free = []
    current = work_start
    for s, e in merged_busy:
        if current < s:
            free.append((current, s))
            current = e
        else:
            if e > current:
                current = e
    if current < work_end:
        free.append((current, work_end))
    return free

def compute_common_free(intervals1, intervals2):
    i = j = 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            common.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return common

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    diane_busy = {
        'Monday': [(720, 750), (900, 930)],
        'Tuesday': [(600, 660), (690, 720), (750, 780), (960, 1020)],
        'Wednesday': [(540, 570), (870, 900), (990, 1020)],
        'Thursday': [(930, 990)],
        'Friday': [(570, 690), (870, 900), (960, 1020)]
    }
    
    matthew_busy = {
        'Monday': [(540, 600), (630, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 660), (720, 870), (960, 1020)],
        'Thursday': [(540, 960)],
        'Friday': [(540, 1020)]
    }
    
    # Add Matthew's Wednesday constraint: not available before 12:30 (750 minutes)
    matthew_busy['Wednesday'].append((540, 750))
    
    for day in days:
        diane_busy_today = diane_busy.get(day, [])
        matthew_busy_today = matthew_busy.get(day, [])
        
        free_diane = compute_free_intervals(work_start, work_end, diane_busy_today)
        free_matthew = compute_free_intervals(work_start, work_end, matthew_busy_today)
        
        common_free = compute_common_free(free_diane, free_matthew)
        
        for start, end in common_free:
            if end - start >= 60:
                meeting_start = start
                meeting_end = start + 60
                # Format meeting times
                start_hour = meeting_start // 60
                start_min = meeting_start % 60
                end_hour = meeting_end // 60
                end_min = meeting_end % 60
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                print(day)
                print(time_str)
                return
    
    # If no suitable time found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()