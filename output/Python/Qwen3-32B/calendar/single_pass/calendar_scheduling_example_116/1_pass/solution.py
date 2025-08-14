def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    # Sort by start time
    busy = sorted(busy_intervals, key=lambda x: x[0])
    # Merge overlapping or adjacent intervals
    merged = []
    for interval in busy:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            curr_start, curr_end = interval
            if curr_start <= last_end:
                # Overlap or adjacent, merge
                merged[-1] = (last_start, max(last_end, curr_end))
            else:
                merged.append(interval)
    # Compute free intervals
    free = []
    prev_end = work_start
    for start, end in merged:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = end
    # Add the end part if there's remaining
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def intersect_intervals(a, b):
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        # Find overlap
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        # Move pointer
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define work hours
work_start = 9 * 60  # 540
work_end = 17 * 60   # 1020

# Participants' busy times
adam_busy = [(14 * 60, 15 * 60)]
john_busy = [(13 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
stephanie_busy = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
anna_busy = [(9 * 60 + 30, 10 * 60), (12 * 60, 12 * 60 + 30), (13 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)]

# Compute free intervals
adam_free = get_free_intervals(adam_busy, work_start, work_end)
john_free = get_free_intervals(john_busy, work_start, work_end)
stephanie_free = get_free_intervals(stephanie_busy, work_start, work_end)
anna_free = get_free_intervals(anna_busy, work_start, work_end)

# Find common free intervals
common_free = adam_free
common_free = intersect_intervals(common_free, john_free)
common_free = intersect_intervals(common_free, stephanie_free)
common_free = intersect_intervals(common_free, anna_free)

# Find the earliest valid slot considering Anna's preference
min_anna_preference = 14 * 60 + 30  # 870
proposed_slots = []

for interval in common_free:
    start, end = interval
    # Determine the earliest possible start time within this interval that meets Anna's preference
    available_start = max(start, min_anna_preference)
    if available_start + 30 <= end:
        # Can fit a 30-minute slot
        proposed_slots.append((available_start, available_start + 30))

# Find the earliest slot
if proposed_slots:
    earliest_start, earliest_end = min(proposed_slots, key=lambda x: x[0])
    start_time = to_time_str(earliest_start)
    end_time = to_time_str(earliest_end)
    print(f"{start_time}:{end_time}:Monday")