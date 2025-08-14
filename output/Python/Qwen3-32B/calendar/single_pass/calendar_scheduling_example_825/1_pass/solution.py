def time_str_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

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

def find_overlaps(intervals1, intervals2):
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

laura_busy = {
    'Monday': [
        ('10:30', '11:00'),
        ('12:30', '13:00'),
        ('14:30', '15:30'),
        ('16:00', '17:00'),
    ],
    'Tuesday': [
        ('09:30', '10:00'),
        ('11:00', '11:30'),
        ('13:00', '13:30'),
        ('14:30', '15:00'),
        ('16:00', '17:00'),
    ],
    'Wednesday': [
        ('11:30', '12:00'),
        ('12:30', '13:00'),
        ('15:30', '16:30'),
    ],
    'Thursday': [
        ('10:30', '11:00'),
        ('12:00', '13:30'),
        ('15:00', '15:30'),
        ('16:00', '16:30'),
    ],
}

philip_busy = {
    'Monday': [('09:00', '17:00')],
    'Tuesday': [
        ('09:00', '11:00'),
        ('11:30', '12:00'),
        ('13:00', '13:30'),
        ('14:00', '14:30'),
        ('15:00', '16:30'),
    ],
    'Wednesday': [
        ('09:00', '10:00'),
        ('11:00', '12:00'),
        ('12:30', '16:00'),
        ('16:30', '17:00'),
    ],
    'Thursday': [
        ('09:00', '10:30'),
        ('11:00', '12:30'),
        ('13:00', '17:00'),
    ],
}

WORK_START = time_str_to_min('09:00')
WORK_END = time_str_to_min('17:00')

days_to_check = ['Tuesday', 'Thursday']

for day in days_to_check:
    laura_day_raw = laura_busy.get(day, [])
    laura_day = [ (time_str_to_min(s), time_str_to_min(e)) for s, e in laura_day_raw ]
    laura_free = get_free_intervals(laura_day, WORK_START, WORK_END)
    
    philip_day_raw = philip_busy.get(day, [])
    philip_day = [ (time_str_to_min(s), time_str_to_min(e)) for s, e in philip_day_raw ]
    philip_free = get_free_intervals(philip_day, WORK_START, WORK_END)
    
    overlaps = find_overlaps(laura_free, philip_free)
    
    for start, end in overlaps:
        if end - start >= 60:
            start_time = min_to_time_str(start)
            end_time = min_to_time_str(end)
            print(f"{day} {start_time}:{end_time}")
            exit()