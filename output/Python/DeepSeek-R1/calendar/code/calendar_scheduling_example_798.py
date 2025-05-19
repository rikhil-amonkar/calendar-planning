def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

work_start = time_to_min('09:00')
work_end = time_to_min('17:00')

nancy_busy = {
    'Monday': [('10:00', '10:30'), ('11:30', '12:30'), ('13:30', '14:00'), ('14:30', '15:30'), ('16:00', '17:00')],
    'Tuesday': [('9:30', '10:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:00', '13:30'), ('15:30', '16:00')],
    'Wednesday': [('10:00', '11:30'), ('13:30', '16:00')]
}

jose_busy = {
    'Monday': [('9:00', '17:00')],
    'Tuesday': [('9:00', '17:00')],
    'Wednesday': [('9:00', '9:30'), ('10:00', '12:30'), ('13:30', '14:30'), ('15:00', '17:00')]
}

for day in ['Monday', 'Tuesday', 'Wednesday']:
    nancy_intervals = [(time_to_min(s), time_to_min(e)) for s, e in nancy_busy[day]]
    jose_intervals = [(time_to_min(s), time_to_min(e)) for s, e in jose_busy[day]]
    
    nancy_free = get_free_intervals(nancy_intervals, work_start, work_end)
    jose_free = get_free_intervals(jose_intervals, work_start, work_end)
    
    overlapping = []
    for n_start, n_end in nancy_free:
        for j_start, j_end in jose_free:
            start = max(n_start, j_start)
            end = min(n_end, j_end)
            if start < end:
                overlapping.append((start, end))
    
    for interval in overlapping:
        if interval[1] - interval[0] >= 30:
            start = interval[0]
            print(f"{day}:{min_to_time(start)}:{min_to_time(start + 30)}")
            exit()