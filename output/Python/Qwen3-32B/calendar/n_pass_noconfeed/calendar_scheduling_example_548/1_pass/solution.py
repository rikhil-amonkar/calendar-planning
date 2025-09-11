def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_slots(work_start, work_end, busy_slots):
    busy_slots = sorted(busy_slots)
    free_slots = []
    current_start = work_start
    for busy_start, busy_end in busy_slots:
        if current_start < busy_start:
            free_slots.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    if current_start < work_end:
        free_slots.append((current_start, work_end))
    return free_slots

work_day = {
    'day': 'Monday',
    'start': 9 * 60,
    'end': 17 * 60
}

nicole_busy = [
    (9 * 60, 10 * 60),
    (10 * 60 + 30, 16 * 60 + 30)
]

free_slots = get_free_slots(work_day['start'], work_day['end'], nicole_busy)

candidates = []
for slot in free_slots:
    start, end = slot
    if end - start >= 30:
        candidates.append(slot)

preference_threshold = 16 * 60
preferred = [s for s in candidates if s[0] >= preference_threshold]

if preferred:
    selected = preferred[0]
else:
    selected = candidates[0]

start_str = to_time_str(selected[0])
end_str = to_time_str(selected[1])

print(f"{{{start_str}:{end_str}}} {work_day['day']}")