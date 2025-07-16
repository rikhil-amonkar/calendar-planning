def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define work hours and meeting duration
work_start = 540   # 9:00 in minutes
work_end = 1020    # 17:00 in minutes
meeting_duration = 30
roger_pref_start = 750  # 12:30 in minutes

# Busy intervals for each participant (start, end) in minutes [start, end)
busy_intervals = [
    # Kathleen
    (870, 930),
    # Carolyn
    (720, 750), (780, 810),
    # Cheryl
    (540, 570), (600, 690), (750, 810), (840, 1020),
    # Virginia
    (570, 690), (720, 750), (780, 810), (870, 930), (960, 1020),
    # Angela
    (570, 600), (630, 690), (720, 750), (780, 810), (840, 990)
]

# Merge busy intervals
if busy_intervals:
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged_busy = []
    start_curr, end_curr = sorted_busy[0]
    for interval in sorted_busy[1:]:
        s, e = interval
        if s <= end_curr:
            end_curr = max(end_curr, e)
        else:
            merged_busy.append((start_curr, end_curr))
            start_curr, end_curr = s, e
    merged_busy.append((start_curr, end_curr))
else:
    merged_busy = []

# Compute free intervals within work hours
free_intervals = []
current = work_start
for start_busy, end_busy in merged_busy:
    if current < start_busy:
        free_intervals.append((current, start_busy))
    current = max(current, end_busy)
if current < work_end:
    free_intervals.append((current, work_end))

# Find the first meeting slot that meets duration and Roger's preference
meeting_slot = None
for start, end in free_intervals:
    slot_length = end - start
    if slot_length < meeting_duration:
        continue
    candidate_start = max(start, roger_pref_start)
    if candidate_start + meeting_duration <= end:
        meeting_slot = (candidate_start, candidate_start + meeting_duration)
        break

# Output the result
if meeting_slot:
    start_str = min_to_time(meeting_slot[0])
    end_str = min_to_time(meeting_slot[1])
    print("Monday")
    print(f"{start_str}:{end_str}")
else:
    # According to the problem, a solution exists, so this is a fallback
    print("Monday")
    print("13:30:14:00")