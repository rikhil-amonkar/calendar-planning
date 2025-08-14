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

def get_free_intervals(merged_buses, work_start, work_end):
    free = []
    prev_end = work_start
    for bus_start, bus_end in merged_buses:
        if prev_end < bus_start:
            free.append((prev_end, bus_start))
        prev_end = max(prev_end, bus_end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def interval_intersection(list1, list2):
    i = 0
    j = 0
    res = []
    while i < len(list1) and j < len(list2):
        a1, a2 = list1[i]
        b1, b2 = list2[j]
        start = max(a1, b1)
        end = min(a2, b2)
        if start < end:
            res.append((start, end))
        if a2 < b2:
            i += 1
        else:
            j += 1
    return res

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

participants = {
    'James': [(11*60 + 30, 12*60 + 0), (14*60 + 30, 15*60 + 0)],
    'John': [(9*60 + 30, 11*60 + 0), (11*60 + 30, 12*60 + 0), (12*60 + 30, 13*60 + 0), (14*60 + 30, 16*60 + 30)]
}

work_start = 9 * 60
work_end = 17 * 60

common_free = None
for name, busy in participants.items():
    merged_buses = merge_intervals(busy)
    free_intervals = get_free_intervals(merged_buses, work_start, work_end)
    if common_free is None:
        common_free = free_intervals
    else:
        common_free = interval_intersection(common_free, free_intervals)

proposed_start = None
proposed_end = None
for interval in common_free:
    s, e = interval
    if e - s >= 60:
        proposed_start = s
        proposed_end = s + 60
        break

start_time = minutes_to_time(proposed_start)
end_time = minutes_to_time(proposed_end)
day = "Monday"
print(f"{start_time}:{end_time} {day}")