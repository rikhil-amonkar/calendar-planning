def time_str_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def interval_intersection(a, b):
    i = j = 0
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

# Work hours
work_start = 540  # 9:00 AM
work_end = 1020   # 5:00 PM

# Ryan's busy intervals
ryan_busy = [(540, 570), (750, 780)]  # 9:00-9:30, 12:30-13:00
free_ryan = get_free_intervals(work_start, work_end, ryan_busy)

# Denise's busy intervals and constraints
denise_work_end = 750  # 12:30 PM (Denise's constraint)
denise_busy_original = [(570, 630), (720, 780), (870, 990)]  # 9:30-10:30, 12:00-13:00, 14:30-16:30
adjusted_denise_busy = []
for start, end in denise_busy_original:
    adjusted_end = min(end, denise_work_end)
    if start < denise_work_end:
        adjusted_denise_busy.append((start, adjusted_end))
free_denise = get_free_intervals(work_start, denise_work_end, adjusted_denise_busy)

# Ruth has no busy times
free_ruth = get_free_intervals(work_start, work_end, [])

# Find intersection between Ryan and Denise
common_intervals = interval_intersection(free_ryan, free_denise)

# Now find a one-hour slot in common_intervals
proposed_start = None
proposed_end = None
for interval in common_intervals:
    start_int, end_int = interval
    if end_int - start_int >= 60:
        proposed_start = start_int
        proposed_end = start_int + 60
        break

if proposed_start is not None:
    start_time = min_to_time_str(proposed_start)
    end_time = min_to_time_str(proposed_end)
    print(f"{start_time}:{end_time} Monday")