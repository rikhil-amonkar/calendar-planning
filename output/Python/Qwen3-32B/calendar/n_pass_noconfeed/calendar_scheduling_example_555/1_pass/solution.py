def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Sort busy intervals by start time
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    # Check if there's free time after last busy
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

# Workday in minutes
workday_start = 9 * 60
workday_end = 17 * 60

# Evelyn's latest time is 13:00
evelyn_latest = 13 * 60

# Randy's busy times
randy_busy = [
    (9*60, 10*60 + 30),   # 9:00-10:30
    (11*60, 15*60 + 30),  # 11:00-15:30
    (16*60, 17*60)        # 16:00-17:00
]

# Compute Randy's free intervals
free_intervals = get_free_intervals(randy_busy, workday_start, workday_end)

# Find the first suitable interval that fits Evelyn's constraints and 30 mins
proposed_time = None
for interval in free_intervals:
    start, end = interval
    # Check if the interval is within Evelyn's available time
    if start >= workday_start and end <= evelyn_latest:
        duration = end - start
        if duration >= 30:
            proposed_start = start
            proposed_end = start + 30  # meeting duration
            proposed_time = (proposed_start, proposed_end)
            break

# Convert to time strings
start_time = minutes_to_time(proposed_time[0])
end_time = minutes_to_time(proposed_time[1])

# Output the result
print(f"{start_time}:{end_time} Monday")