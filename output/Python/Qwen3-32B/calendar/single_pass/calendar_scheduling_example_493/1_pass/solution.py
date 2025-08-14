def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

start_time = 9 * 60
end_time = 17 * 60

participants = {
    'Tyler': [],
    'Kelly': [],
    'Stephanie': [ (11*60, 11*60 + 30), (14*60 + 30, 15*60) ],
    'Hannah': [],
    'Joe': [ (9*60, 9*60 + 30), (10*60, 12*60), (12*60 + 30, 13*60), (14*60, 17*60) ],
    'Diana': [ (9*60, 10*60 + 30), (11*60 + 30, 12*60), (13*60, 14*60), (14*60 + 30, 15*60 + 30), (16*60, 17*60) ],
    'Deborah': [ (9*60, 10*60), (10*60 + 30, 12*60), (12*60 + 30, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 15*60 + 30), (16*60, 16*60 + 30) ]
}

def get_free_intervals(busy_intervals):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    for interval in sorted_busy:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            curr_start, curr_end = interval
            if curr_start <= last_end:
                merged[-1] = (last_start, max(last_end, curr_end))
            else:
                merged.append(interval)
    free = []
    prev_end = start_time
    for interval in merged:
        start, end = interval
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = end
    if prev_end < end_time:
        free.append((prev_end, end_time))
    return free

def interval_intersection(a, b):
    i = 0
    j = 0
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

free_intervals_list = []
for name in participants:
    busy_intervals = participants[name]
    free_intervals = get_free_intervals(busy_intervals)
    free_intervals_list.append(free_intervals)

common_free = free_intervals_list[0]
for i in range(1, len(free_intervals_list)):
    common_free = interval_intersection(common_free, free_intervals_list[i])

meeting_start = None
meeting_end = None
for interval in common_free:
    start, end = interval
    if end - start >= 30:
        meeting_start = start
        meeting_end = start + 30
        break

day = "Monday"
start_str = minutes_to_time_str(meeting_start)
end_str = minutes_to_time_str(meeting_end)
print(f"{start_str}:{end_str} {day}")