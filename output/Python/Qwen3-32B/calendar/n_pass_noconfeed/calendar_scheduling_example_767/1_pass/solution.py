def time_str_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [list(sorted_intervals[0])]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            if current[1] > last[1]:
                last[1] = current[1]
        else:
            merged.append(list(current))
    return [tuple(interval) for interval in merged]

def subtract_blocked(work_start, work_end, blocked_intervals):
    merged_blocked = merge_intervals(blocked_intervals)
    free_intervals = [(work_start, work_end)]
    for (b_start, b_end) in merged_blocked:
        new_free = []
        for (f_start, f_end) in free_intervals:
            if f_start < b_start:
                new_free.append((f_start, b_start))
            if f_end > b_end:
                new_free.append((b_end, f_end))
        free_intervals = new_free
    return free_intervals

def intersect_intervals(list1, list2):
    result = []
    for a_start, a_end in list1:
        for b_start, b_end in list2:
            start = max(a_start, b_start)
            end = min(a_end, b_end)
            if start < end:
                result.append((start, end))
    return result

blocked_times = {
    'Monday': {
        'Martha': [('16:00', '17:00')],
        'Beverly': [('9:00', '13:30'), ('14:00', '17:00')]
    },
    'Tuesday': {
        'Martha': [('15:00', '15:30')],
        'Beverly': [('9:00', '17:00')]
    },
    'Wednesday': {
        'Martha': [('10:00', '11:00'), ('14:00', '14:30')],
        'Beverly': [('9:30', '15:30'), ('16:30', '17:00')]
    }
}

work_start_min = 9 * 60
work_end_min = 17 * 60
days = ['Monday', 'Tuesday', 'Wednesday']

for day in days:
    martha_blocked = []
    for start, end in blocked_times[day]['Martha']:
        martha_blocked.append((time_str_to_min(start), time_str_to_min(end)))
    
    beverly_blocked = []
    for start, end in blocked_times[day]['Beverly']:
        beverly_blocked.append((time_str_to_min(start), time_str_to_min(end)))
    
    martha_free = subtract_blocked(work_start_min, work_end_min, martha_blocked)
    beverly_free = subtract_blocked(work_start_min, work_end_min, beverly_blocked)
    
    common_free = intersect_intervals(martha_free, beverly_free)
    
    for start, end in common_free:
        if end - start >= 60:
            start_time = min_to_time_str(start)
            end_time = min_to_time_str(end)
            time_range = f"{start_time}:{end_time}"
            print(f"{day} {time_range}")
            break