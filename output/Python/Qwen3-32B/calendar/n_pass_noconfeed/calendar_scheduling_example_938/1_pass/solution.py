def get_free_intervals(busy_intervals):
    work_start = 540  # 9:00 AM
    work_end = 1020   # 5:00 PM
    free = [(work_start, work_end)]
    for start, end in busy_intervals:
        new_free = []
        for (f_start, f_end) in free:
            if end <= f_start or start >= f_end:
                new_free.append((f_start, f_end))
            else:
                if f_start < start:
                    new_free.append((f_start, start))
                if f_end > end:
                    new_free.append((end, f_end))
        free = new_free
    return free

def find_overlaps(free1, free2):
    overlaps = []
    for (s1, e1) in free1:
        for (s2, e2) in free2:
            start = max(s1, s2)
            end = min(e1, e2)
            if start < end and (end - start) >= 30:
                overlaps.append((start, end))
    return overlaps

# Busy times for each participant
busy_eugene = {
    'Monday': [
        (660, 720), (810, 840), (870, 900), (960, 990)
    ],
    'Tuesday': [],
    'Wednesday': [
        (540, 570), (660, 690), (720, 750), (810, 900)
    ],
    'Thursday': [
        (570, 600), (660, 750)
    ],
    'Friday': [
        (630, 660), (720, 750), (780, 810)
    ]
}

busy_eric = {
    'Monday': [(540, 1020)],
    'Tuesday': [(540, 1020)],
    'Wednesday': [
        (540, 690), (720, 840), (870, 990)
    ],
    'Thursday': [(540, 1020)],
    'Friday': [
        (540, 660), (690, 1020)
    ]
}

# Days to check in order of preference (avoid Wednesday)
days_order = ['Friday', 'Wednesday']

for day in days_order:
    eugene_b = busy_eugene.get(day, [])
    eric_b = busy_eric.get(day, [])
    
    eugene_free = get_free_intervals(eugene_b)
    eric_free = get_free_intervals(eric_b)
    
    overlaps = find_overlaps(eugene_free, eric_free)
    
    if overlaps:
        earliest = min(overlaps, key=lambda x: x[0])
        start_min, end_min = earliest
        
        def to_time(mins):
            h = mins // 60
            m = mins % 60
            return f"{h:02d}:{m:02d}"
        
        start_time = to_time(start_min)
        end_time = to_time(end_min)
        
        print(f"{day} {start_time}:{end_time}")
        break