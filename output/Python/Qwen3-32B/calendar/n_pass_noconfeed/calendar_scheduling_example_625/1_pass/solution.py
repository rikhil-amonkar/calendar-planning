def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(blocked_intervals, work_start=540, work_end=1020):
    blocked = sorted(blocked_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in blocked:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

# Define blocked intervals for each day
blocked_mon = [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)]
blocked_tue = [
    (9 * 60, 9 * 60 + 30),
    (10 * 60 + 30, 11 * 60 + 30),
    (12 * 60 + 30, 13 * 60 + 30),
    (14 * 60 + 30, 15 * 60 + 30),
    (16 * 60, 17 * 60)
]

days = ['Monday', 'Tuesday']
blocked = {
    'Monday': blocked_mon,
    'Tuesday': blocked_tue
}

# Generate free intervals for each day
free_intervals = {}
for day in days:
    free_intervals[day] = get_free_intervals(blocked[day])

# Collect all possible meeting slots
possible_slots = []
for day in days:
    for s, e in free_intervals[day]:
        if e - s >= 30:
            possible_slots.append((day, s, s + 30))

# Apply preferences
preference_1 = []
preference_2 = []
preference_3 = []
for slot in possible_slots:
    day, start, end = slot
    if day == 'Tuesday' and start >= 870:  # 14:30 is 870 minutes
        preference_1.append(slot)
    elif day == 'Tuesday':
        preference_2.append(slot)
    else:
        preference_3.append(slot)

# Select the best slot
selected = None
if preference_1:
    selected = min(preference_1, key=lambda x: x[1])
elif preference_2:
    selected = min(preference_2, key=lambda x: x[1])
else:
    selected = min(preference_3, key=lambda x: x[1])

day, start, end = selected
start_str = to_time_str(start)
end_str = to_time_str(end)
print(f"{day} {start_str}:{end_str}")