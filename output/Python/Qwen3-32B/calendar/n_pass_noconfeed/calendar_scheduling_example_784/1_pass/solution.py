def get_free_intervals(blocked_intervals, work_start=540, work_end=1020):
    if not blocked_intervals:
        return [(work_start, work_end)]
    # Sort and merge blocked intervals
    sorted_blocked = sorted(blocked_intervals, key=lambda x: x[0])
    merged = []
    for start, end in sorted_blocked:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge
                merged[-1][1] = max(last_end, end)
            else:
                merged.append([start, end])
    # Compute free intervals
    free = []
    prev_end = work_start
    for block_start, block_end in merged:
        if block_start > prev_end:
            free.append((prev_end, block_start))
        prev_end = max(prev_end, block_end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def mins_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

# Define blocked intervals for each participant and day
judith_blocked = {
    'Monday': [(720, 750)],  # 12:00-12:30
    'Tuesday': [],
    'Wednesday': [(690, 720)],  # 11:30-12:00
}

timothy_blocked = {
    'Monday': [(570, 600), (630, 690), (750, 840), (930, 1020)],  # 9:30-10:00, 10:30-11:30, 12:30-14:00, 15:30-17:00
    'Tuesday': [(570, 780), (810, 840), (870, 1020)],  # 9:30-13:00, 13:30-14:00, 14:30-17:00
    'Wednesday': [(540, 570), (630, 660), (810, 870), (900, 930), (960, 990)],  # 9:00-9:30, 10:30-11:00, 13:30-14:30, 15:00-15:30, 16:00-16:30
}

candidates = []

days = ['Monday', 'Tuesday', 'Wednesday']

for day in days:
    # Judith's free intervals
    j_blocked = judith_blocked.get(day, [])
    j_free = get_free_intervals(j_blocked)
    # Timothy's free intervals
    t_blocked = timothy_blocked.get(day, [])
    t_free = get_free_intervals(t_blocked)
    # Find overlapping intervals
    for j_start, j_end in j_free:
        for t_start, t_end in t_free:
            overlap_start = max(j_start, t_start)
            overlap_end = min(j_end, t_end)
            if overlap_start < overlap_end:
                duration = overlap_end - overlap_start
                if duration >= 60:  # 60 minutes
                    candidates.append((day, overlap_start, overlap_end))

def get_priority(day, end_time):
    if day == 'Wednesday':
        if end_time <= 720:  # before or at 12:00
            return 0
        else:
            return 1
    elif day == 'Tuesday':
        return 2
    elif day == 'Monday':
        return 3
    else:
        return 4

# Sort candidates by priority
sorted_candidates = sorted(candidates, key=lambda x: get_priority(x[0], x[2]))

if sorted_candidates:
    best_day, best_start, best_end = sorted_candidates[0]
    start_time = mins_to_time(best_start)
    end_time = mins_to_time(best_end)
    print(f"{{{start_time}:{end_time}}} {best_day}")
else:
    print("No suitable time found")