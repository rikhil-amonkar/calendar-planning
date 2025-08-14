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

def find_free_slots(merged, start_day, end_day):
    free_slots = []
    prev_end = start_day
    for interval in merged:
        start, end = interval
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        free_slots.append((prev_end, end_day))
    return free_slots

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

all_intervals = [
    # Joshua's intervals
    (660, 750), (810, 870), (990, 1020),
    # Jerry's intervals
    (540, 570), (630, 720), (750, 780), (810, 840), (870, 900), (930, 960),
    # Jesse's intervals
    (540, 570), (630, 720), (750, 780), (870, 900), (930, 990),
    # Kenneth's intervals
    (630, 750), (810, 840), (870, 900), (930, 960), (990, 1020)
]

merged = merge_intervals(all_intervals)
start_day = 540  # 9:00 AM
end_day = 1020   # 5:00 PM

free_slots = find_free_slots(merged, start_day, end_day)

for slot in free_slots:
    start_slot, end_slot = slot
    duration = end_slot - start_slot
    if duration >= 60:
        meeting_start = start_slot
        meeting_end = meeting_start + 60
        start_str = minutes_to_time_str(meeting_start)
        end_str = minutes_to_time_str(meeting_end)
        print(f"{start_str}:{end_str} Monday")
        break