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

def get_free_intervals(work_start, work_end, merged_busy):
    free = []
    prev_end = work_start
    for start, end in merged_busy:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 9 * 60
work_end = 17 * 60

all_busy = []

# Christine's busy
christine = [
    (9*60+30, 10*60+30),
    (12*60+0, 12*60+30),
    (13*60+0, 13*60+30),
    (14*60+30, 15*60+0),
    (16*60+0, 16*60+30),
]
all_busy.extend(christine)

# Bobby's busy
bobby = [
    (12*60+0, 12*60+30),
    (14*60+30, 15*60+0),
]
all_busy.extend(bobby)

# Elizabeth's busy
elizabeth = [
    (9*60+0, 9*60+30),
    (11*60+30, 13*60+0),
    (13*60+30, 14*60+0),
    (15*60+0, 15*60+30),
    (16*60+0, 17*60+0),
]
all_busy.extend(elizabeth)

# Tyler's busy
tyler = [
    (9*60+0, 11*60+0),
    (12*60+0, 12*60+30),
    (13*60+0, 13*60+30),
    (15*60+30, 16*60+0),
    (16*60+30, 17*60+0),
]
all_busy.extend(tyler)

# Edward's busy
edward = [
    (9*60+0, 9*60+30),
    (10*60+0, 11*60+0),
    (11*60+30, 14*60+0),
    (14*60+30, 15*60+30),
    (16*60+0, 17*60+0),
]
all_busy.extend(edward)

merged = merge_intervals(all_busy)
free_intervals = get_free_intervals(work_start, work_end, merged)

candidates = []
for start, end in free_intervals:
    duration = end - start
    if duration >= 30:
        if start <= 13 * 60:  # 13:00 is 780
            candidates.append((start, end))

best_time = candidates[0] if candidates else None

if best_time:
    start_str = to_time_str(best_time[0])
    end_str = to_time_str(best_time[1])
    day = "Monday"
    print(f"{start_str}:{end_str}:{day}")