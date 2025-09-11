def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, blocked_intervals):
    blocked = sorted(blocked_intervals, key=lambda x: x[0])
    merged = []
    for start, end in blocked:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1][1] = max(last_end, end)
            else:
                merged.append([start, end])
    free = []
    current_start = work_start
    for start, end in merged:
        if current_start < start:
            free.append((current_start, start))
        current_start = end
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def find_overlaps(intervals1, intervals2):
    i = 0
    j = 0
    overlaps = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            overlaps.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return overlaps

blocked_gary_mon = [
    (9*60 + 30, 10*60),   # 9:30-10:00
    (11*60, 13*60),       # 11:00-13:00
    (14*60, 14*60 + 30),  # 14:00-14:30
    (16*60 + 30, 17*60),  # 16:30-17:00
]
blocked_gary_tue = [
    (9*60, 9*60 + 30),        # 9:00-9:30
    (10*60 + 30, 11*60),      # 10:30-11:00
    (14*60 + 30, 16*60),      # 14:30-16:00
]
blocked_david_mon = [
    (9*60, 9*60 + 30),        # 9:00-9:30
    (10*60, 13*60),           # 10:00-13:00
    (14*60 + 30, 16*60 + 30), # 14:30-16:30
]
blocked_david_tue = [
    (9*60, 9*60 + 30),        # 9:00-9:30
    (10*60, 10*60 + 30),      # 10:00-10:30
    (11*60, 12*60 + 30),      # 11:00-12:30
    (13*60, 14*60 + 30),      # 13:00-14:30
    (15*60, 16*60),           # 15:00-16:00
    (16*60 + 30, 17*60),      # 16:30-17:00
]

days = ['Monday', 'Tuesday']
blocked_gary = [blocked_gary_mon, blocked_gary_tue]
blocked_david = [blocked_david_mon, blocked_david_tue]

work_start = 9 * 60
work_end = 17 * 60

for day_idx in range(2):  # 0 for Monday, 1 for Tuesday
    day_name = days[day_idx]
    blocked_g = blocked_gary[day_idx]
    blocked_d = blocked_david[day_idx]
    free_g = get_free_intervals(work_start, work_end, blocked_g)
    free_d = get_free_intervals(work_start, work_end, blocked_d)
    overlaps = find_overlaps(free_g, free_d)
    for start, end in overlaps:
        if end - start >= 60:
            start_time = min_to_time(start)
            end_time = min_to_time(end)
            print(f"{start_time}:{end_time} {day_name}")
            exit()