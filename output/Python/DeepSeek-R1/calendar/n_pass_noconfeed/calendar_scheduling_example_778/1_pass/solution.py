def compute_free_intervals(busy_list, day_start, day_end):
    if not busy_list:
        return [(day_start, day_end)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_busy[0]
    for i in range(1, len(sorted_busy)):
        s, e = sorted_busy[i]
        if s <= current_end:
            if e > current_end:
                current_end = e
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    
    free_intervals = []
    if day_start < merged[0][0]:
        free_intervals.append((day_start, merged[0][0]))
    
    for i in range(len(merged) - 1):
        gap_start = merged[i][1]
        gap_end = merged[i+1][0]
        if gap_start < gap_end:
            free_intervals.append((gap_start, gap_end))
    
    if merged[-1][1] < day_end:
        free_intervals.append((merged[-1][1], day_end))
    
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
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

susan_busy = {
    'Monday': [(12*60+30, 13*60), (13*60+30, 14*60)],
    'Tuesday': [(11*60+30, 12*60)],
    'Wednesday': [(9*60+30, 10*60+30), (14*60, 14*60+30), (15*60+30, 16*60+30)],
}

sandra_busy = {
    'Monday': [(9*60, 13*60), (14*60, 15*60), (16*60, 16*60+30)],
    'Tuesday': [(9*60, 9*60+30), (10*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 14*60+30), (16*60, 17*60)],
    'Wednesday': [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)],
}

days_order = ['Monday', 'Wednesday', 'Tuesday']
day_start_min = 9 * 60
day_end_min = 17 * 60

for day in days_order:
    susan_list = susan_busy.get(day, [])
    sandra_list = sandra_busy.get(day, [])
    
    if day == 'Monday':
        sandra_list.append((16*60, 17*60))
    
    susan_free = compute_free_intervals(susan_list, day_start_min, day_end_min)
    sandra_free = compute_free_intervals(sandra_list, day_start_min, day_end_min)
    
    common_free = intersect_intervals(susan_free, sandra_free)
    
    for (start, end) in common_free:
        if end - start >= 30:
            start_hour = start // 60
            start_minute = start % 60
            end_time = start + 30
            end_hour = end_time // 60
            end_minute = end_time % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print(f"{{{time_str}}}")
            print(day)
            exit(0)

print("No solution found")
exit(1)