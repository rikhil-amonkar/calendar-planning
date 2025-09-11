def get_free_intervals(busy_intervals, start_day=540, end_day=1020):
    busy_intervals.sort()
    free = []
    prev_end = start_day
    for start, end in busy_intervals:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        free.append((prev_end, end_day))
    return free

def interval_intersection(a, b):
    i = 0
    j = 0
    res = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

# Define busy intervals for each participant
busy_wayne = []
busy_melissa = [
    (10 * 60, 11 * 60),  # 10:00-11:00
    (12 * 60 + 30, 14 * 60),  # 12:30-14:00
    (15 * 60, 15 * 60 + 30)  # 15:00-15:30
]
busy_catherine = []
busy_gregory = [
    (12 * 60 + 30, 13 * 60),  # 12:30-13:00
    (15 * 60 + 30, 16 * 60)  # 15:30-16:00
]
busy_victoria = [
    (9 * 60, 9 * 60 + 30),  # 9:00-9:30
    (10 * 60 + 30, 11 * 60 + 30),  # 10:30-11:30
    (13 * 60, 14 * 60),  # 13:00-14:00
    (14 * 60 + 30, 15 * 60),  # 14:30-15:00
    (15 * 60 + 30, 16 * 60 + 30)  # 15:30-16:30
]
busy_thomas = [
    (10 * 60, 12 * 60),  # 10:00-12:00
    (12 * 60 + 30, 13 * 60),  # 12:30-13:00
    (14 * 60 + 30, 16 * 60)  # 14:30-16:00
]
busy_jennifer = [
    (9 * 60, 9 * 60 + 30),  # 9:00-9:30
    (10 * 60, 10 * 60 + 30),  # 10:00-10:30
    (11 * 60, 13 * 60),  # 11:00-13:00
    (13 * 60 + 30, 14 * 60 + 30),  # 13:30-14:30
    (15 * 60, 15 * 60 + 30),  # 15:00-15:30
    (16 * 60, 16 * 60 + 30)  # 16:00-16:30
]

participants = [
    {'busy': busy_wayne},
    {'busy': busy_melissa},
    {'busy': busy_catherine},
    {'busy': busy_gregory},
    {'busy': busy_victoria},
    {'busy': busy_thomas},
    {'busy': busy_jennifer},
]

common_free = None
for p in participants:
    busy = p['busy']
    free = get_free_intervals(busy)
    if common_free is None:
        common_free = free
    else:
        common_free = interval_intersection(common_free, free)

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

possible_slots = []
for start, end in common_free:
    if end - start >= 30:
        possible_slots.append((start, start + 30))

# Find the best slot according to Wayne's preference
sorted_slots = sorted(possible_slots, key=lambda x: x[0])
best_slot = None
# Check for slots after 14:00 (840 minutes)
for slot in sorted_slots:
    if slot[0] >= 840:
        best_slot = slot
        break
if best_slot is None:
    best_slot = sorted_slots[0]

start_time = to_time(best_slot[0])
end_time = to_time(best_slot[1])
print(f"{start_time}:{end_time} Monday")