def time_str_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def get_free_intervals(work_start, work_end, blocked_intervals):
    if not blocked_intervals:
        return [(work_start, work_end)]
    blocked = sorted(blocked_intervals, key=lambda x: x[0])
    merged = []
    for interval in blocked:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                new_start = last[0]
                new_end = max(last[1], interval[1])
                merged[-1] = (new_start, new_end)
            else:
                merged.append(interval)
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

def get_overlap(a, b):
    start = max(a[0], b[0])
    end = min(a[1], b[1])
    if start < end:
        return (start, end)
    return None

def find_common_intervals(intervals_list):
    common = intervals_list[0]
    for i in range(1, len(intervals_list)):
        current = intervals_list[i]
        new_common = []
        for c in common:
            for curr in current:
                overlap = get_overlap(c, curr)
                if overlap:
                    new_common.append(overlap)
        common = new_common
        if not common:
            return []
    return common

def minutes_to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

work_start = 9 * 60
work_end = 17 * 60

diane_blocked = [
    (time_str_to_minutes("9:30"), time_str_to_minutes("10:00")),
    (time_str_to_minutes("14:30"), time_str_to_minutes("15:00"))
]

jack_blocked = [
    (time_str_to_minutes("13:30"), time_str_to_minutes("14:00")),
    (time_str_to_minutes("14:30"), time_str_to_minutes("15:00"))
]

eugene_blocked = [
    (time_str_to_minutes("9:00"), time_str_to_minutes("10:00")),
    (time_str_to_minutes("10:30"), time_str_to_minutes("11:30")),
    (time_str_to_minutes("12:00"), time_str_to_minutes("14:30")),
    (time_str_to_minutes("15:00"), time_str_to_minutes("16:30"))
]

patricia_blocked = [
    (time_str_to_minutes("9:30"), time_str_to_minutes("10:30")),
    (time_str_to_minutes("11:00"), time_str_to_minutes("12:00")),
    (time_str_to_minutes("12:30"), time_str_to_minutes("14:00")),
    (time_str_to_minutes("15:00"), time_str_to_minutes("16:30"))
]

diane_free = get_free_intervals(work_start, work_end, diane_blocked)
jack_free = get_free_intervals(work_start, work_end, jack_blocked)
eugene_free = get_free_intervals(work_start, work_end, eugene_blocked)
patricia_free = get_free_intervals(work_start, work_end, patricia_blocked)

common_intervals = find_common_intervals([
    diane_free, 
    jack_free, 
    eugene_free, 
    patricia_free
])

meeting_duration = 30
best_start = None
best_end = None

for interval in common_intervals:
    start, end = interval
    if end - start >= meeting_duration:
        best_start = start
        best_end = start + meeting_duration
        break

start_time = minutes_to_time_str(best_start)
end_time = minutes_to_time_str(best_end)
day = "Monday"
print(f"{start_time}:{end_time} {day}")