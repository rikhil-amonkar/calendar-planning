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

def get_free_intervals(merged, start_day, end_day):
    free = []
    prev_end = start_day
    for interval in merged:
        start, end = interval
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        free.append((prev_end, end_day))
    return free

def to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

ronald_busy = {
    'Monday': [(630, 660), (720, 750), (930, 960)],
    'Tuesday': [(540, 570), (720, 750), (930, 990)],
    'Wednesday': [(570, 630), (660, 720), (750, 780), (810, 840), (990, 1020)]
}

amber_busy = {
    'Monday': [(540, 570), (600, 630), (690, 720), (750, 870), (870, 900), (930, 1020)],
    'Tuesday': [(540, 570), (600, 690), (720, 750), (810, 930), (990, 1020)],
    'Wednesday': [(540, 570), (600, 630), (660, 810), (900, 930)]
}

days = ['Monday', 'Tuesday', 'Wednesday']
for day in days:
    ronald = ronald_busy.get(day, [])
    amber = amber_busy.get(day, [])
    all_busy = ronald + amber
    merged = merge_intervals(all_busy)
    free_intervals = get_free_intervals(merged, 540, 1020)
    for interval in free_intervals:
        start, end = interval
        if end - start >= 30:
            meeting_start = start
            meeting_end = start + 30
            start_time = to_time(meeting_start)
            end_time = to_time(meeting_end)
            print(f"{start_time}:{end_time} {day}")
            exit()