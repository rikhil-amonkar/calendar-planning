def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define busy times for each participant in minutes since midnight
busy_times = {
    'Wayne': [],
    'Melissa': [(600, 660), (750, 840), (900, 930)],
    'Catherine': [],
    'Gregory': [(750, 810), (930, 960)],
    'Victoria': [(540, 570), (630, 690), (780, 840), (870, 900), (930, 990)],
    'Thomas': [(600, 720), (750, 780), (870, 960)],
    'Jennifer': [(540, 570), (600, 630), (660, 780), (810, 870), (900, 930), (960, 990)]
}

valid_slots = []

# Workday is from 9:00 (540) to 17:00 (1020)
for start_time in range(540, 990 + 1):  # 990 is 16:30, adding 30 gives 17:00
    end_time = start_time + 30
    if end_time > 1020:
        continue
    all_free = True
    for person in busy_times:
        for (b_start, b_end) in busy_times[person]:
            # Check if [start_time, end_time) overlaps with [b_start, b_end)
            if not (end_time <= b_start or start_time >= b_end):
                all_free = False
                break
        if not all_free:
            break
    if all_free:
        valid_slots.append((start_time, end_time))

# Find the best slot: prefer after 14:00 (840 minutes)
candidates_after_14 = [slot for slot in valid_slots if slot[0] >= 840]
if candidates_after_14:
    best_slot = min(candidates_after_14, key=lambda x: x[0])
else:
    best_slot = min(valid_slots, key=lambda x: x[0])

start_str = to_time_str(best_slot[0])
end_str = to_time_str(best_slot[1])
print(f"{start_str}:{end_str} Monday")