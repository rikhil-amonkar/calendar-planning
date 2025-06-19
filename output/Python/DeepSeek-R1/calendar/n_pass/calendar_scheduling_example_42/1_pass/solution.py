def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_list, work_start, work_end):
    if not busy_list:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free = []
    current = work_start
    for interval in sorted_busy:
        start, end = interval
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        low = max(start1, start2)
        high = min(end1, end2)
        if low < high:
            result.append((low, high))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Main
work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60

# Define busy intervals
julie_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

sean_busy = [
    (time_to_minutes("9:00"), time_to_minutes("9:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

lori_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("13:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Compute free intervals
julie_free = get_free_intervals(julie_busy, work_start, work_end)
sean_free = get_free_intervals(sean_busy, work_start, work_end)
lori_free = get_free_intervals(lori_busy, work_start, work_end)

# Find common free times
common_js = intersect_intervals(julie_free, sean_free)
common_all = intersect_intervals(common_js, lori_free)

# Find first suitable slot
for start, end in common_all:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
        print(time_str)
        print("Monday")
        break