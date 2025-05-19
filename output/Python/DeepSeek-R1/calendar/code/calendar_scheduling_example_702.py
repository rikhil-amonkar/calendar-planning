def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def to_time_str(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

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

def get_free_intervals(busy, day_start=540, day_end=1020):
    merged = merge_intervals(busy)
    free = []
    prev_end = day_start
    for start, end in merged:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < day_end:
        free.append((prev_end, day_end))
    return free

def find_overlap(a, b):
    overlaps = []
    i = j = 0
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlaps.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlaps

robert_busy = {
    'Monday': [(parse_time('11:00'), parse_time('11:30')), (parse_time('14:00'), parse_time('14:30')), (parse_time('15:30'), parse_time('16:00'))],
    'Tuesday': [(parse_time('10:30'), parse_time('11:00')), (parse_time('15:00'), parse_time('15:30'))],
    'Wednesday': [(parse_time('10:00'), parse_time('11:00')), (parse_time('11:30'), parse_time('12:00')), (parse_time('12:30'), parse_time('13:00')), (parse_time('13:30'), parse_time('14:00')), (parse_time('15:00'), parse_time('15:30')), (parse_time('16:00'), parse_time('16:30'))]
}

ralph_busy = {
    'Monday': [(parse_time('10:00'), parse_time('13:30')), (parse_time('14:00'), parse_time('14:30')), (parse_time('15:00'), parse_time('17:00'))],
    'Tuesday': [(parse_time('09:00'), parse_time('09:30')), (parse_time('10:00'), parse_time('10:30')), (parse_time('11:00'), parse_time('11:30')), (parse_time('12:00'), parse_time('13:00')), (parse_time('14:00'), parse_time('15:30')), (parse_time('16:00'), parse_time('17:00'))],
    'Wednesday': [(parse_time('10:30'), parse_time('11:00')), (parse_time('11:30'), parse_time('12:00')), (parse_time('13:00'), parse_time('14:30')), (parse_time('16:30'), parse_time('17:00'))]
}

days_order = ['Tuesday', 'Wednesday', 'Monday']

for day in days_order:
    r_merged = merge_intervals(robert_busy[day])
    r_free = get_free_intervals(r_merged)
    ra_merged = merge_intervals(ralph_busy[day])
    ra_free = get_free_intervals(ra_merged)
    overlaps = find_overlap(r_free, ra_free)
    
    for interval in overlaps:
        start, end = interval
        if end - start >= 30:
            meeting_start = start
            meeting_end = start + 30
            print(f"{day}:{to_time_str(meeting_start)}:{to_time_str(meeting_end)}")
            exit()

print("No suitable time found")