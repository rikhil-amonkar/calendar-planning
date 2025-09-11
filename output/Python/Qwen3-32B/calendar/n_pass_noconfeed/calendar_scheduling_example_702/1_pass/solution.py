WORK_START = 9 * 60
WORK_END = 17 * 60

def generate_free_intervals(busy_intervals, work_start, work_end):
    busy = sorted(busy_intervals, key=lambda x: x[0])
    free = [(work_start, work_end)]
    for interval in busy:
        new_free = []
        b_start, b_end = interval
        for f_start, f_end in free:
            if f_end <= b_start or f_start >= b_end:
                new_free.append((f_start, f_end))
            else:
                if f_start < b_start:
                    new_free.append((f_start, b_start))
                if f_end > b_end:
                    new_free.append((b_end, f_end))
        free = new_free
    return free

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

robert_schedule = {
    'Monday': [
        (11*60, 11*60 + 30),
        (14*60, 14*60 + 30),
        (15*60 + 30, 16*60)
    ],
    'Tuesday': [
        (10*60 + 30, 11*60),
        (15*60, 15*60 + 30)
    ],
    'Wednesday': [
        (10*60, 11*60),
        (11*60 + 30, 12*60),
        (12*60 + 30, 13*60),
        (13*60 + 30, 14*60),
        (15*60, 15*60 + 30),
        (16*60, 16*60 + 30)
    ]
}

ralph_schedule = {
    'Monday': [
        (10*60, 13*60 + 30),
        (14*60, 14*60 + 30),
        (15*60, 17*60)
    ],
    'Tuesday': [
        (9*60, 9*60 + 30),
        (10*60, 10*60 + 30),
        (11*60, 11*60 + 30),
        (12*60, 13*60),
        (14*60, 15*60 + 30),
        (16*60, 17*60)
    ],
    'Wednesday': [
        (10*60 + 30, 11*60),
        (11*60 + 30, 12*60),
        (13*60, 14*60 + 30),
        (16*60 + 30, 17*60)
    ]
}

days = ['Tuesday', 'Wednesday', 'Monday']

for day in days:
    robert_busy = robert_schedule.get(day, [])
    ralph_busy = ralph_schedule.get(day, [])
    
    robert_free = generate_free_intervals(robert_busy, WORK_START, WORK_END)
    ralph_free = generate_free_intervals(ralph_busy, WORK_START, WORK_END)
    
    overlaps = []
    for r in robert_free:
        for ra in ralph_free:
            start = max(r[0], ra[0])
            end = min(r[1], ra[1])
            if start < end and (end - start) >= 30:
                overlaps.append((start, end))
    
    if overlaps:
        earliest = min(overlaps, key=lambda x: x[0])
        start_time = minutes_to_time(earliest[0])
        end_time = minutes_to_time(earliest[0] + 30)
        print(f"{start_time}:{end_time} {day}")
        break