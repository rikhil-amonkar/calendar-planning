def time_to_min(h, m):
    return h * 60 + m

def min_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_overlap(a, b):
    overlap = []
    i = j = 0
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlap.append((start, end))
            if a_end < b_end:
                i += 1
            else:
                j += 1
        else:
            if a_start < b_start:
                i += 1
            else:
                j += 1
    return overlap

schedules = {
    'Bobby': {
        'Monday': [(14, 30, 15, 0)],
        'Tuesday': [
            (9, 0, 11, 30),
            (12, 0, 12, 30),
            (13, 0, 15, 0),
            (15, 30, 17, 0)
        ]
    },
    'Michael': {
        'Monday': [
            (9, 0, 10, 0),
            (10, 30, 13, 30),
            (14, 0, 15, 0),
            (15, 30, 17, 0)
        ],
        'Tuesday': [
            (9, 0, 10, 30),
            (11, 0, 11, 30),
            (12, 0, 14, 0),
            (15, 0, 16, 0),
            (16, 30, 17, 0)
        ]
    }
}

work_start = time_to_min(9, 0)
work_end = time_to_min(17, 0)
days = ['Monday', 'Tuesday']
earliest = None

for day in days:
    bobby_busy = []
    for interval in schedules['Bobby'][day]:
        sh, sm, eh, em = interval
        start = time_to_min(sh, sm)
        end = time_to_min(eh, em)
        bobby_busy.append((start, end))
    bobby_free = get_free_intervals(bobby_busy, work_start, work_end)
    
    michael_busy = []
    for interval in schedules['Michael'][day]:
        sh, sm, eh, em = interval
        start = time_to_min(sh, sm)
        end = time_to_min(eh, em)
        michael_busy.append((start, end))
    michael_free = get_free_intervals(michael_busy, work_start, work_end)
    
    overlap = find_overlap(bobby_free, michael_free)
    
    for start, end in overlap:
        if end - start >= 30:
            if earliest is None or start < earliest[0]:
                earliest = (start, end, day)

start, end, day = earliest
start_time = min_to_time(start)
end_time = min_to_time(end)
print(f"{day}:{start_time}:{end_time}")