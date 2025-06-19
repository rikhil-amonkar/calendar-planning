def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Tuesday's busy times after 12:00 for Daniel and Bradley
daniel_busy_tuesday = [
    ('13:00', '13:30'),
    ('15:30', '16:00'),
    ('16:30', '17:00')
]

bradley_busy_tuesday = [
    ('12:00', '13:00'),
    ('13:30', '14:00'),
    ('15:30', '16:30')
]

# Convert to minutes
daniel_min = [(time_to_minutes(s), time_to_minutes(e)) for s, e in daniel_busy_tuesday]
bradley_min = [(time_to_minutes(s), time_to_minutes(e)) for s, e in bradley_busy_tuesday]

# Combine and sort all busy intervals
all_busy = daniel_min + bradley_min
all_busy.sort(key=lambda x: x[0])

# Merge intervals
merged = []
if all_busy:
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        s, e = all_busy[i]
        if s <= current_end:  # Overlapping or adjacent
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))

# Work period on Tuesday: 12:00 (720) to 17:00 (1020)
work_start = 720
work_end = 1020

# Find free intervals
free_intervals = []
current = work_start
for start, end in merged:
    if current < start:
        free_intervals.append((current, start))
    current = max(current, end)
if current < work_end:
    free_intervals.append((current, work_end))

# Find first 30-minute slot
meeting_start = None
for start, end in free_intervals:
    if end - start >= 30:
        meeting_start = start
        meeting_end = meeting_start + 30
        break

# Output the result
if meeting_start is not None:
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    time_range_str = f"{start_str}:{end_str}"
    print("Tuesday")
    print(time_range_str)
else:
    # According to the problem, a solution exists, so this should not happen
    print("No suitable time found")