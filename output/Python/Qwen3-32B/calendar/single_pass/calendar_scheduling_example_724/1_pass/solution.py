def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_available_intervals(busy_intervals, work_start=540, work_end=1020):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

tyler_busy = {
    'Monday': [],
    'Tuesday': [(540, 570), (870, 900)],  # 9:00-9:30, 14:30-15:00
    'Wednesday': [(630, 660), (750, 780), (810, 840), (990, 1020)]  # 10:30-11:00, 12:30-13:00, 13:30-14:00, 16:30-17:00
}

ruth_busy = {
    'Monday': [(540, 600), (630, 720), (750, 870), (900, 960), (990, 1020)],
    'Tuesday': [(540, 1020)],
    'Wednesday': [(540, 1020)]
}

possible_slots = []

for day in ['Monday', 'Tuesday', 'Wednesday']:
    t_busy = tyler_busy.get(day, [])
    r_busy = ruth_busy.get(day, [])
    
    t_available = get_available_intervals(t_busy)
    r_available = get_available_intervals(r_busy)
    
    for t_start, t_end in t_available:
        for r_start, r_end in r_available:
            start_overlap = max(t_start, r_start)
            end_overlap = min(t_end, r_end)
            if end_overlap - start_overlap >= 30:
                possible_slots.append((day, start_overlap, end_overlap))

best_slot = None
for slot in possible_slots:
    day, start, end = slot
    if day == 'Monday' and start >= 960:  # 16:00 is 960 minutes
        best_slot = slot
        break  # pick the first one that meets the preference

if best_slot is None:
    best_slot = min(possible_slots, key=lambda x: (x[0], x[1]))

day, start, end = best_slot
start_time = minutes_to_time(start)
end_time = minutes_to_time(end)
print(f"{start_time}:{end_time} {day}")