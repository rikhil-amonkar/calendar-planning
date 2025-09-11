WORK_START = 9 * 60
WORK_END = 17 * 60

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if prev_end < start:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Participants' busy intervals
lisa_busy = [
    (9*60, 9*60 + 30),
    (10*60 + 30, 11*60),
    (14*60, 16*60)
]

anthony_busy = [
    (9*60, 9*60 + 30),
    (11*60, 11*60 + 30),
    (12*60 + 30, 13*60 + 30),
    (14*60, 15*60),
    (15*60 + 30, 16*60),
    (16*60 + 30, 17*60)
]

# Compute free intervals
lisa_free = get_free_intervals(lisa_busy, WORK_START, WORK_END)
anthony_free = get_free_intervals(anthony_busy, WORK_START, WORK_END)

# Find common free intervals
common_free = []
for l_start, l_end in lisa_free:
    for a_start, a_end in anthony_free:
        start = max(l_start, a_start)
        end = min(l_end, a_end)
        if start < end:
            common_free.append((start, end))

# Check for meeting duration (30 minutes)
meeting_duration = 30
valid_common = [ (s, e) for s, e in common_free if e - s >= meeting_duration ]

# Find earliest start time
if valid_common:
    earliest_start = valid_common[0][0]
    earliest_end = earliest_start + meeting_duration
    start_time = minutes_to_time(earliest_start)
    end_time = minutes_to_time(earliest_end)
    day = "Monday"
    print(f"{start_time}:{end_time}:{day}")