def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work period for Tuesday: 9:00 to 11:00
work_start = time_str_to_minutes("9:00")
work_end = time_str_to_minutes("11:00")

# Amanda's busy intervals on Tuesday (only those within 9:00-11:00)
amanda_busy = [
    [time_str_to_minutes("9:00"), time_str_to_minutes("9:30")],
    [time_str_to_minutes("10:00"), time_str_to_minutes("10:30")]
]

# Nathan's busy intervals on Tuesday (only those within 9:00-11:00)
nathan_busy = [
    [time_str_to_minutes("9:00"), time_str_to_minutes("10:30")]
]

# Calculate free intervals for Amanda
amanda_free = []
current = work_start
for start, end in sorted(amanda_busy, key=lambda x: x[0]):
    if current < start:
        amanda_free.append([current, start])
    current = max(current, end)
if current < work_end:
    amanda_free.append([current, work_end])

# Calculate free intervals for Nathan
nathan_free = []
current = work_start
for start, end in sorted(nathan_busy, key=lambda x: x[0]):
    if current < start:
        nathan_free.append([current, start])
    current = max(current, end)
if current < work_end:
    nathan_free.append([current, work_end])

# Find overlapping free intervals
overlapping_free = []
for a_start, a_end in amanda_free:
    for n_start, n_end in nathan_free:
        start_overlap = max(a_start, n_start)
        end_overlap = min(a_end, n_end)
        if start_overlap < end_overlap:
            overlapping_free.append([start_overlap, end_overlap])

# Find the first overlapping interval with at least 30 minutes
meeting_slot = None
for start, end in overlapping_free:
    if end - start >= 30:
        meeting_slot = [start, start + 30]
        break

# Output the meeting day and time
if meeting_slot:
    day = "Tuesday"
    start_time = minutes_to_time(meeting_slot[0])
    end_time = minutes_to_time(meeting_slot[1])
    print(day)
    print(f"{start_time}:{end_time}")