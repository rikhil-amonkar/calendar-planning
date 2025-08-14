def generate_available_intervals(blocked, work_start, work_end):
    # Sort blocked intervals by start time
    blocked_sorted = sorted(blocked, key=lambda x: x[0])
    # Merge overlapping or adjacent intervals
    merged = []
    for interval in blocked_sorted:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1] + 1:
                new_start = last[0]
                new_end = max(last[1], interval[1])
                merged[-1] = (new_start, new_end)
            else:
                merged.append(interval)
    # Now compute available intervals
    available = []
    prev_end = work_start
    for interval in merged:
        start_blocked, end_blocked = interval
        if start_blocked > prev_end:
            available.append((prev_end, start_blocked))
        prev_end = max(prev_end, end_blocked)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours
work_start = 9 * 60
work_end = 17 * 60

# Blocked times for each participant
blocked_gregory = [
    (9*60, 10*60),
    (10*60 +30, 11*60 +30),
    (12*60 +30, 13*60),
    (13*60 +30, 14*60)
]
blocked_christine = [
    (9*60, 11*60 +30),
    (13*60 +30, 17*60)
]
blocked_vincent = [
    (9*60, 9*60 +30),
    (10*60 +30, 12*60),
    (12*60 +30, 14*60),
    (14*60 +30, 17*60)
]

# Generate available intervals
available_gregory = generate_available_intervals(blocked_gregory, work_start, work_end)
available_christine = generate_available_intervals(blocked_christine, work_start, work_end)
available_vincent = generate_available_intervals(blocked_vincent, work_start, work_end)

# List of available intervals for each participant
participants_available = [available_gregory, available_christine, available_vincent]

# Compute the intersection of all available intervals
current_candidates = available_gregory.copy()

for i in range(1, len(participants_available)):
    current_available = participants_available[i]
    new_candidates = []
    for candidate in current_candidates:
        c_start, c_end = candidate
        for avail in current_available:
            a_start, a_end = avail
            overlap_start = max(c_start, a_start)
            overlap_end = min(c_end, a_end)
            if overlap_start < overlap_end:
                new_candidates.append((overlap_start, overlap_end))
    current_candidates = new_candidates

# Find the earliest suitable interval (>=30 minutes)
for interval in sorted(current_candidates, key=lambda x: x[0]):
    duration = interval[1] - interval[0]
    if duration >= 30:
        start_time = interval[0]
        end_time = interval[1]
        break

# Convert to time strings
start_str = to_time_str(start_time)
end_str = to_time_str(end_time)

# Output the result
print(f"{start_str}:{end_str} Monday")