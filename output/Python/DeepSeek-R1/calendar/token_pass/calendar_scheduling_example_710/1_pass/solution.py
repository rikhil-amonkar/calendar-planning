work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # minutes

# Define busy times for each participant per day in minutes from midnight
cheryl_busy = {
    'Monday': [(540, 570), (690, 780), (930, 960)],
    'Tuesday': [(900, 930)],
}

kyle_busy = {
    'Monday': [(540, 1020)],
    'Tuesday': [(570, 1020)],
}

days_to_check = ['Monday', 'Tuesday']  # Wednesday excluded since Cheryl cannot meet

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for interval in sorted_intervals[1:]:
        if interval[0] <= end:
            if interval[1] > end:
                end = interval[1]
        else:
            merged.append((start, end))
            start, end = interval
    merged.append((start, end))
    return merged

for day in days_to_check:
    busy_list = cheryl_busy.get(day, []) + kyle_busy.get(day, [])
    merged_busy = merge_intervals(busy_list)
    free_intervals = []
    current = work_start
    for start, end in merged_busy:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            print(f"{day} {start_time}:{end_time}")
            exit(0)

print("No suitable time found")