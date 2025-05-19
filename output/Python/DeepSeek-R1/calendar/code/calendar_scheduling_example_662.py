def get_free_intervals(blocked, work_start=0, work_end=480):
    if not blocked:
        return [(work_start, work_end)]
    blocked_sorted = sorted(blocked, key=lambda x: x[0])
    merged = []
    for interval in blocked_sorted:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                merged[-1] = (last[0], max(last[1], interval[1]))
            else:
                merged.append(interval)
    free = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_overlapping_intervals(a, b):
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
        else:
            if a_start < b_start:
                i += 1
            else:
                j += 1
    return overlaps

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    mins = minutes % 60
    return f"{hours:02}:{mins:02}"

gary_blocked = {
    'Monday': [(30, 60), (120, 240), (300, 330), (450, 480)],
    'Tuesday': [(0, 30), (90, 120), (330, 420)]
}

david_blocked = {
    'Monday': [(0, 30), (60, 240), (330, 450)],
    'Tuesday': [(0, 30), (60, 90), (120, 210), (240, 330), (360, 420), (450, 480)]
}

days = ['Monday', 'Tuesday']
work_hours = (0, 480)

for day in days:
    gary_free = get_free_intervals(gary_blocked.get(day, []), *work_hours)
    david_free = get_free_intervals(david_blocked.get(day, []), *work_hours)
    overlaps = find_overlapping_intervals(gary_free, david_free)
    for start, end in overlaps:
        if end - start >= 60:
            start_time = minutes_to_time(start)
            end_time = minutes_to_time(start + 60)
            print(f"{day}:{start_time}:{end_time}")
            exit()

print("No suitable time found.")