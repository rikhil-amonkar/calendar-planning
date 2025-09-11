def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    merged = merge_intervals(busy_intervals)
    free = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_common_free(free1, free2):
    i = 0
    j = 0
    common = []
    while i < len(free1) and j < len(free2):
        s1, e1 = free1[i]
        s2, e2 = free2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            common.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return common

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

mary_busy = {
    'Monday': [],
    'Tuesday': [(10*60, 10*60 + 30), (15*60 + 30, 16*60)],
    'Wednesday': [(9*60 + 30, 10*60), (15*60, 15*60 + 30)],
    'Thursday': [(9*60, 10*60), (10*60 + 30, 11*60 + 30)],
}

alexis_busy = {
    'Monday': [(9*60, 10*60), (10*60 + 30, 12*60), (12*60 + 30, 16*60 + 30)],
    'Tuesday': [(9*60, 10*60), (10*60 + 30, 11*60 + 30), (12*60, 15*60 + 30), (16*60, 17*60)],
    'Wednesday': [(9*60, 11*60), (11*60 + 30, 17*60)],
    'Thursday': [(10*60, 12*60), (14*60, 14*60 + 30), (15*60 + 30, 16*60), (16*60 + 30, 17*60)],
}

work_start = 9 * 60
work_end = 17 * 60

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

possible_starts = []

for day in days:
    m_b = mary_busy.get(day, [])
    a_b = alexis_busy.get(day, [])
    
    m_free = get_free_intervals(m_b, work_start, work_end)
    a_free = get_free_intervals(a_b, work_start, work_end)
    
    common = find_common_free(m_free, a_free)
    
    for start, end in common:
        if end - start >= 30:
            possible_starts.append((start, day))

earliest_start, earliest_day = min(possible_starts, key=lambda x: x[0])

start_time = minutes_to_time(earliest_start)
end_time = minutes_to_time(earliest_start + 30)

print(f"{{{start_time}:{end_time}}} {earliest_day}")