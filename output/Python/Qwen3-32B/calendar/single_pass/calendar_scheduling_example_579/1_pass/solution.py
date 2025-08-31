def compute_free_intervals(work_start, work_end, busy_intervals):
    busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free


# Work hours in minutes
christine_work_start = 9 * 60  # 540
christine_work_end = 17 * 60   # 1020

helen_work_start = 9 * 60  # 540
helen_work_end = 15 * 60   # 900

# Christine's busy intervals
christine_busy = [
    (11 * 60, 11 * 60 + 30),  # 11:00-11:30
    (15 * 60, 15 * 60 + 30)   # 15:00-15:30
]

# Helen's original busy intervals
helen_original_busy = [
    (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
    (11 * 60, 11 * 60 + 30),      # 11:00-11:30
    (12 * 60, 12 * 60 + 30),      # 12:00-12:30
    (13 * 60 + 30, 16 * 60),      # 13:30-16:00
    (16 * 60 + 30, 17 * 60)       # 16:30-17:00
]

# Adjust Helen's busy intervals to fit within her work hours
adjusted_helen_busy = []
for start, end in helen_original_busy:
    adj_start = max(start, helen_work_start)
    adj_end = min(end, helen_work_end)
    if adj_start < adj_end:
        adjusted_helen_busy.append((adj_start, adj_end))

# Compute free intervals for each participant
christine_free = compute_free_intervals(christine_work_start, christine_work_end, christine_busy)
helen_free = compute_free_intervals(helen_work_start, helen_work_end, adjusted_helen_busy)

# Find overlapping intervals between Christine and Helen's free intervals
overlapping = []
for c_start, c_end in christine_free:
    for h_start, h_end in helen_free:
        start = max(c_start, h_start)
        end = min(c_end, h_end)
        if start < end:
            overlapping.append((start, end))

# Now find the earliest interval that can fit the 30-minute meeting
meeting_duration = 30  # minutes
for interval in sorted(overlapping, key=lambda x: x[0]):
    if interval[1] - interval[0] >= meeting_duration:
        start_time = interval[0]
        end_time = start_time + meeting_duration

        # Convert to HH:MM format
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_str = to_time_str(start_time)
        end_str = to_time_str(end_time)
        day = "Monday"
        print(f"{start_str}:{end_str} {day}")
        break
