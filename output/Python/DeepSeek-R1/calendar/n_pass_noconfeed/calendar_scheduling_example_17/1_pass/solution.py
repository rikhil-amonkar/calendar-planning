def get_free_intervals(blocked, start_bound, end_bound):
    if not blocked:
        return [(start_bound, end_bound)]
    blocked_sorted = sorted(blocked, key=lambda x: x[0])
    free = []
    current = start_bound
    for block in blocked_sorted:
        if block[0] > current:
            free.append((current, block[0]))
        current = max(current, block[1])
    if current < end_bound:
        free.append((current, end_bound))
    return free

def intersect_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            result.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Given constraints for Monday (in minutes from 9:00, where 0 = 9:00)
margaret_blocked = [(0, 60), (90, 120), (150, 180), (240, 270)]
donna_blocked = []  # No blocks in the relevant time frame
helen_blocked = [(0, 30), (60, 150), (240, 270)]

# Time horizon: meeting must end by 13:30 (270 minutes from 9:00)
work_start = 0
work_end = 270

# Get free intervals for each participant
margaret_free = get_free_intervals(margaret_blocked, work_start, work_end)
donna_free = get_free_intervals(donna_blocked, work_start, work_end)
helen_free = get_free_intervals(helen_blocked, work_start, work_end)

# Find common free intervals
common = intersect_intervals(donna_free, margaret_free)
common = intersect_intervals(common, helen_free)

# Find a 30-minute slot
meeting_slot = None
for interval in common:
    start, end = interval
    if end - start >= 30:
        meeting_slot = (start, start + 30)
        break

# Convert and output
start_time_str = minutes_to_time(meeting_slot[0])
end_time_str = minutes_to_time(meeting_slot[1])
time_range_str = f"{start_time_str}:{end_time_str}"
print(f"Monday {time_range_str}")