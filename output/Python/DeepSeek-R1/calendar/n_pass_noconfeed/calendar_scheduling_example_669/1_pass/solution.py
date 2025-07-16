work_start = 9 * 60
work_end = 17 * 60

jean_busy = {
    'Monday': [],
    'Tuesday': [(11*60+30, 12*60), (16*60, 16*60+30)]
}

doris_busy = {
    'Monday': [
        (9*60, 11*60+30),
        (12*60, 12*60+30),
        (13*60+30, 16*60),
        (16*60+30, 17*60)
    ],
    'Tuesday': [(9*60, 17*60)]
}

days = ['Monday', 'Tuesday']
meeting_duration = 30

def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in sorted_busy:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

found = False
result_day = None
result_start = None
result_end = None

for day in days:
    jean_free = compute_free_intervals(jean_busy[day], work_start, work_end)
    doris_free = compute_free_intervals(doris_busy[day], work_start, work_end)
    common_free = []
    i = 0
    j = 0
    while i < len(jean_free) and j < len(doris_free):
        j_start, j_end = jean_free[i]
        d_start, d_end = doris_free[j]
        low = max(j_start, d_start)
        high = min(j_end, d_end)
        if low < high:
            common_free.append((low, high))
        if j_end < d_end:
            i += 1
        else:
            j += 1
    
    if day == 'Monday':
        for interval in common_free:
            start_interval, end_interval = interval
            meeting_start = start_interval
            meeting_end = meeting_start + meeting_duration
            if meeting_end <= end_interval and meeting_end <= 14*60:
                result_day = day
                result_start = meeting_start
                result_end = meeting_end
                found = True
                break
        if found:
            break
            
        for interval in common_free:
            start_interval, end_interval = interval
            meeting_start = start_interval
            meeting_end = meeting_start + meeting_duration
            if meeting_end <= end_interval:
                result_day = day
                result_start = meeting_start
                result_end = meeting_end
                found = True
                break
        if found:
            break
    else:
        for interval in common_free:
            start_interval, end_interval = interval
            meeting_start = start_interval
            meeting_end = meeting_start + meeting_duration
            if meeting_end <= end_interval:
                result_day = day
                result_start = meeting_start
                result_end = meeting_end
                found = True
                break
        if found:
            break

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

start_str = format_time(result_start)
end_str = format_time(result_end)
time_range_str = f"{start_str}:{end_str}"

print(result_day)
print(time_range_str)