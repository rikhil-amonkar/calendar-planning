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

def get_free_intervals(merged_busy, work_start, work_end):
    free_intervals = []
    prev_end = work_start
    for start, end in merged_busy:
        if prev_end < start:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 9 * 60
work_end = 17 * 60
duration = 30

participants = {
    'Monday': {
        'Shirley': [
            (10 * 60 + 30, 11 * 60),
            (12 * 60, 12 * 60 + 30),
            (16 * 60, 16 * 60 + 30)
        ],
        'Albert': [
            (9 * 60, 17 * 60)
        ]
    },
    'Tuesday': {
        'Shirley': [
            (9 * 60 + 30, 10 * 60)
        ],
        'Albert': [
            (9 * 60 + 30, 10 * 60),
            (11 * 60, 12 * 60 + 30),
            (13 * 60, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ]
    }
}

possible_slots = []

for day in ['Monday', 'Tuesday']:
    busy_intervals = []
    for person in participants[day]:
        busy_intervals.extend(participants[day][person])
    merged = merge_intervals(busy_intervals)
    free_intervals = get_free_intervals(merged, work_start, work_end)
    for (s, e) in free_intervals:
        if e - s >= duration:
            possible_slots.append((day, s, s + duration))

preferred_slots = []
for slot in possible_slots:
    day, start, end = slot
    if day == 'Tuesday' and start > 10 * 60 + 30:
        continue
    preferred_slots.append(slot)

earliest_slot = None
for slot in preferred_slots:
    day, start, end = slot
    if earliest_slot is None or start < earliest_slot[1]:
        earliest_slot = (day, start, end)

day, start, end = earliest_slot
start_str = to_time_str(start)
end_str = to_time_str(end)
print(f"{start_str}:{end_str} {day}")