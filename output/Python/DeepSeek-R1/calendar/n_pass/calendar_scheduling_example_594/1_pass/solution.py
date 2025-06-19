def time_to_minutes(time_str):
    h, m = time_str.split(':')
    total_minutes = (int(h) * 60 + int(m)) - 540  # 540 minutes is 9:00 in minutes from midnight
    return total_minutes

def minutes_to_time(minutes):
    total_abs = 540 + minutes
    hour = total_abs // 60
    minute = total_abs % 60
    return f"{hour:02d}:{minute:02d}"

# Meeting duration in minutes
meeting_duration = 30

# Work hours
work_start_min = 0  # 9:00
work_end_min = 480  # 17:00

# Busy times for Adam and Roy
adam_busy_times = [
    ("9:30", "10:00"),
    ("12:30", "13:00"),
    ("14:30", "15:00"),
    ("16:30", "17:00")
]

roy_busy_times = [
    ("10:00", "11:00"),
    ("11:30", "13:00"),
    ("13:30", "14:30"),
    ("16:30", "17:00")
]

# Convert busy times to minutes and sort
def convert_busy_times(busy_times):
    busy_minutes = []
    for start, end in busy_times:
        s_min = time_to_minutes(start)
        e_min = time_to_minutes(end)
        busy_minutes.append((s_min, e_min))
    busy_minutes.sort(key=lambda x: x[0])
    return busy_minutes

adam_busy = convert_busy_times(adam_busy_times)
roy_busy = convert_busy_times(roy_busy_times)

# Compute free intervals for a participant
def compute_free_intervals(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free.append((current, start))
        current = end
    if current < work_end:
        free.append((current, work_end))
    return free

adam_free = compute_free_intervals(adam_busy, work_start_min, work_end_min)
roy_free = compute_free_intervals(roy_busy, work_start_min, work_end_min)

# Find common free intervals
common_free = []
i = j = 0
while i < len(adam_free) and j < len(roy_free):
    a_start, a_end = adam_free[i]
    r_start, r_end = roy_free[j]
    start_overlap = max(a_start, r_start)
    end_overlap = min(a_end, r_end)
    if start_overlap < end_overlap:
        common_free.append((start_overlap, end_overlap))
    if a_end < r_end:
        i += 1
    else:
        j += 1

# Find the earliest slot that fits the meeting duration
found = None
for start, end in common_free:
    if end - start >= meeting_duration:
        found = (start, start + meeting_duration)
        break

if found is None:
    print("No solution found")
else:
    day = "Monday"
    start_time_str = minutes_to_time(found[0])
    end_time_str = minutes_to_time(found[1])
    s_h, s_m = start_time_str.split(':')
    e_h, e_m = end_time_str.split(':')
    time_range_str = f"{s_h}:{s_m}:{e_h}:{e_m}"
    print(day)
    print(time_range_str)