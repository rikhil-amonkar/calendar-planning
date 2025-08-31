def generate_free_intervals(busy_intervals, start_day=540, end_day=1020):
    busy_intervals.sort()
    free = []
    current_start = start_day
    for start, end in busy_intervals:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < end_day:
        free.append((current_start, end_day))
    return free


def compute_overlap(a, b):
    a_start, a_end = a
    b_start, b_end = b
    start = max(a_start, b_start)
    end = min(a_end, b_end)
    if start < end:
        return (start, end)
    return None


def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


# Busy intervals for each participant
busy_intervals = {
    'Katherine': [(720, 750), (780, 870)],
    'Rebecca': [],
    'Julie': [(540, 570), (630, 660), (810, 840), (900, 930)],
    'Angela': [(540, 600), (630, 660), (690, 840), (870, 900), (990, 1020)],
    'Nicholas': [(570, 660), (690, 810), (840, 960), (990, 1020)],
    'Carl': [(540, 660), (690, 750), (780, 870), (900, 960), (990, 1020)]
}

participants = ['Katherine', 'Rebecca', 'Julie', 'Angela', 'Nicholas', 'Carl']

# Generate free intervals for each participant
free_intervals = {}
for p in participants:
    free_intervals[p] = generate_free_intervals(busy_intervals[p])

# Compute the common intervals
common = free_intervals['Katherine']
for p in participants[1:]:
    current_free = free_intervals[p]
    new_common = []
    for a in common:
        for b in current_free:
            overlap = compute_overlap(a, b)
            if overlap:
                new_common.append(overlap)
    common = new_common
    if not common:
        break  # no common intervals

# Find possible 30-minute slots
possible_slots = [interval for interval in common if interval[1] - interval[0] >= 30]

# Select the best slot based on Angela's preference
candidates_after_15 = [slot for slot in possible_slots if slot[0] >= 900]
if candidates_after_15:
    best_slot = min(candidates_after_15, key=lambda x: x[0])
else:
    best_slot = min(possible_slots, key=lambda x: x[0])

# Convert to time format
start_time = minutes_to_time(best_slot[0])
end_time = minutes_to_time(best_slot[0] + 30)

# Output
print(f"Monday {start_time}:{end_time}")
