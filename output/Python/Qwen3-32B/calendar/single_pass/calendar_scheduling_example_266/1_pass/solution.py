def get_free_intervals(busy_times, start_day=540, end_day=1020):
    sorted_busy = sorted(busy_times, key=lambda x: x[0])
    free_intervals = []
    prev_end = start_day
    for start, end in sorted_busy:
        if prev_end < start:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        free_intervals.append((prev_end, end_day))
    return free_intervals


def interval_intersection(a, b):
    i = 0
    j = 0
    result = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result


def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"


participants_busy = {
    'Joe': [(9*60+30, 10*60), (10*60+30, 11*60)],
    'Keith': [(11*60+30, 12*60), (15*60, 15*60+30)],
    'Patricia': [(9*60, 9*60+30), (13*60, 13*60+30)],
    'Nancy': [(9*60, 11*60), (11*60+30, 16*60+30)],
    'Pamela': [(9*60, 10*60), (10*60+30, 11*60), (11*60+30, 12*60+30), (13*60, 14*60), (14*60+30, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)]
}

free_intervals_list = []
for busy in participants_busy.values():
    free_intervals = get_free_intervals(busy)
    free_intervals_list.append(free_intervals)

common = free_intervals_list[0]
for i in range(1, len(free_intervals_list)):
    common = interval_intersection(common, free_intervals_list[i])

meeting_duration = 30
candidates = []
for interval in common:
    start, end = interval
    if end - start >= meeting_duration:
        candidates.append(interval)

selected = candidates[0]
start_time = minutes_to_time(selected[0])
end_time = minutes_to_time(selected[1])
day_of_week = "Monday"

print(f"{start_time}:{end_time} {day_of_week}")
