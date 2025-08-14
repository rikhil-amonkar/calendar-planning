def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    busy_in_min = []
    for start, end in busy_intervals:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        busy_in_min.append((s, e))
    sorted_busy = sorted(busy_in_min, key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def find_overlapping_intervals(intervals1, intervals2):
    i = 0
    j = 0
    overlaps = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlaps.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlaps

bryan_busy = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': [],
    'Thursday': [('09:30', '10:00'), ('12:30', '13:00')],
    'Friday': [('10:30', '11:00'), ('14:00', '14:30')],
}

nicholas_busy = {
    'Monday': [('11:30', '12:00'), ('13:00', '15:30')],
    'Tuesday': [('09:00', '09:30'), ('11:00', '13:30'), ('14:00', '16:30')],
    'Wednesday': [('09:00', '09:30'), ('10:00', '11:00'), ('11:30', '13:30'), ('14:00', '14:30'), ('15:00', '16:30')],
    'Thursday': [('10:30', '11:30'), ('12:00', '12:30'), ('15:00', '15:30'), ('16:30', '17:00')],
    'Friday': [('09:00', '10:30'), ('11:00', '12:00'), ('12:30', '14:30'), ('15:30', '16:00'), ('16:30', '17:00')],
}

days_to_check = ['Wednesday', 'Friday', 'Tuesday']

for day in days_to_check:
    if day in ['Monday', 'Thursday']:
        continue
    bryan_day_busy = bryan_busy[day]
    nicholas_day_busy = nicholas_busy[day]
    bryan_free = get_free_intervals(bryan_day_busy)
    nicholas_free = get_free_intervals(nicholas_day_busy)
    overlaps = find_overlapping_intervals(bryan_free, nicholas_free)
    for start, end in overlaps:
        if end - start >= 60:
            start_time = minutes_to_time(start)
            end_time = minutes_to_time(end)
            time_range = f"{start_time.replace(':', '')}:{end_time.replace(':', '')}"
            print(f"{time_range} {day}")
            exit()