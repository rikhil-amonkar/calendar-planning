def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

busy_julie = [
    (9*60, 9*60 + 30),
    (11*60, 11*60 + 30),
    (12*60, 12*60 + 30),
    (13*60 + 30, 14*60),
    (16*60, 17*60)
]

busy_sean = [
    (9*60, 9*60 + 30),
    (13*60, 13*60 + 30),
    (15*60, 15*60 + 30),
    (16*60, 16*60 + 30)
]

busy_lori = [
    (10*60, 10*60 + 30),
    (11*60, 13*60),
    (15*60 + 30, 17*60)
]

def get_free_intervals(busy_intervals):
    work_start = 9 * 60
    work_end = 17 * 60
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    result = []
    for start, end in free_intervals:
        if end - start >= 60:
            result.append((start, end))
    return result

julie_free = get_free_intervals(busy_julie)
sean_free = get_free_intervals(busy_sean)
lori_free = get_free_intervals(busy_lori)

found = False
for j in julie_free:
    for s in sean_free:
        for l in lori_free:
            start = max(j[0], s[0], l[0])
            end = min(j[1], s[1], l[1])
            if start < end and (end - start) >= 60:
                start_time = to_time_str(start)
                end_time = to_time_str(end)
                print(f"{start_time}:{end_time} Monday")
                found = True
                break
        if found:
            break
    if found:
        break