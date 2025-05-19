def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def parse_schedule(busy_schedule, day):
    intervals = []
    for entry in busy_schedule.get(day, []):
        start = time_to_min(entry[0])
        end = time_to_min(entry[1])
        intervals.append((start, end))
    intervals.sort()
    return intervals

def get_free_intervals(busy_intervals):
    work_start = 540  # 9:00
    work_end = 1020   # 17:00
    free = []
    prev_end = work_start
    for start, end in sorted(busy_intervals, key=lambda x: x[0]):
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def interval_intersection(a, b):
    i = j = 0
    res = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

laura_busy = {
    'Monday': [('10:30', '11:00'), ('12:30', '13:00'), ('14:30', '15:30'), ('16:00', '17:00')],
    'Tuesday': [('9:30', '10:00'), ('11:00', '11:30'), ('13:00', '13:30'), ('14:30', '15:00'), ('16:00', '17:00')],
    'Thursday': [('10:30', '11:00'), ('12:00', '13:30'), ('15:00', '15:30'), ('16:00', '16:30')]
}

philip_busy = {
    'Monday': [('9:00', '17:00')],
    'Tuesday': [('9:00', '11:00'), ('11:30', '12:00'), ('13:00', '13:30'), ('14:00', '14:30'), ('15:00', '16:30')],
    'Thursday': [('9:00', '10:30'), ('11:00', '12:30'), ('13:00', '17:00')]
}

days_to_check = ['Monday', 'Tuesday', 'Thursday']

for day in days_to_check:
    laura_intervals = parse_schedule(laura_busy, day)
    philip_intervals = parse_schedule(philip_busy, day)
    
    laura_free = get_free_intervals(laura_intervals)
    philip_free = get_free_intervals(philip_intervals)
    
    common_free = interval_intersection(laura_free, philip_free)
    
    for start, end in common_free:
        if end - start >= 60:
            meeting_start = start
            meeting_end = start + 60
            start_time = min_to_time(meeting_start)
            end_time = min_to_time(meeting_end)
            print(f"{day} {start_time}:{end_time}")
            exit()

print("No suitable time found")