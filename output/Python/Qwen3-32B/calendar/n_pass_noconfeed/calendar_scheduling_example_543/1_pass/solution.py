def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

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
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

work_start = 9 * 60
work_end = 17 * 60

busy_times = [
    (11*60 + 30, 12*60 + 0),
    (14*60 + 30, 15*60 + 0),
    (9*60 + 30, 11*60 + 0),
    (11*60 + 30, 12*60 + 0),
    (12*60 + 30, 13*60 + 0),
    (14*60 + 30, 16*60 + 30),
]

merged = merge_intervals(busy_times)
free_intervals = get_free_intervals(merged, work_start, work_end)

meeting_duration = 60  # minutes

for interval in free_intervals:
    start, end = interval
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        start_time = minutes_to_time(meeting_start)
        end_time = minutes_to_time(meeting_end)
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
        break