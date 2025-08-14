def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(merged, work_start, work_end):
    free = []
    prev_end = work_start
    for interval in merged:
        start, end = interval
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

participants = {
    'Jacob': [
        (13*60 + 30, 14*60 + 0),
        (14*60 + 30, 15*60 + 0)
    ],
    'Diana': [
        (9*60 + 30, 10*60 + 0),
        (11*60 + 30, 12*60 + 0),
        (13*60 + 0, 13*60 + 30),
        (16*60 + 0, 16*60 + 30)
    ],
    'Adam': [
        (9*60 + 30, 10*60 + 30),
        (11*60 + 0, 12*60 + 30),
        (15*60 + 30, 16*60 + 0)
    ],
    'Angela': [
        (9*60 + 30, 10*60 + 0),
        (10*60 + 30, 12*60 + 0),
        (13*60 + 0, 15*60 + 30),
        (16*60 + 0, 16*60 + 30)
    ],
    'Dennis': [
        (9*60 + 0, 9*60 + 30),
        (10*60 + 30, 11*60 + 30),
        (13*60 + 0, 15*60 + 0),
        (16*60 + 30, 17*60 + 0)
    ]
}

all_busy = []
for person in participants.values():
    all_busy.extend(person)

merged = merge_intervals(all_busy)
work_start = 9 * 60
work_end = 17 * 60
free_intervals = get_free_intervals(merged, work_start, work_end)

for interval in free_intervals:
    start, end = interval
    if end - start >= 30:
        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)
        print(f"{start_str}:{end_str} Monday")
        break