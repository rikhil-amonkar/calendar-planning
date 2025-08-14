def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [list(sorted_intervals[0])]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            last[1] = max(last[1], current[1])
        else:
            merged.append(list(current))
    return [tuple(interval) for interval in merged]

def get_free_slots(merged_busy, work_start, work_end):
    free_slots = []
    prev_end = work_start
    for start, end in merged_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    return free_slots

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define busy intervals for each participant
participants = {
    'Judy': [(780, 810), (960, 990)],
    'Olivia': [(600, 630), (720, 780), (840, 870)],
    'Eric': [],
    'Jacqueline': [(600, 630), (900, 930)],
    'Laura': [(540, 600), (630, 720), (780, 810), (870, 900), (930, 1020)],
    'Tyler': [(540, 600), (660, 690), (750, 780), (840, 870), (930, 1020)],
    'Lisa': [(570, 630), (660, 690), (720, 750), (780, 810), (840, 870), (960, 1020)]
}

# Collect all busy intervals
all_busy = []
for intervals in participants.values():
    all_busy.extend(intervals)

# Merge intervals
merged_busy = merge_intervals(all_busy)

# Work hours in minutes (9:00 to 17:00)
work_start = 540  # 9*60
work_end = 1020   # 17*60

# Get free slots
free_slots = get_free_slots(merged_busy, work_start, work_end)

# Filter slots with at least 30 minutes
suitable_slots = [slot for slot in free_slots if slot[1] - slot[0] >= 30]

# Output the first suitable slot
slot = suitable_slots[0]
start_time = to_time(slot[0])
end_time = to_time(slot[1])
day = "Monday"

print(f"{start_time}:{end_time} {day}")