def time_to_minutes(time_str):
    hours, minutes = time_str.split(':')
    return int(hours) * 60 + int(minutes)

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Work hours: 9:00 to 17:00 (Monday)
work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")

# Margaret's constraint: meeting must start at or after 14:30
effective_start = time_to_minutes("14:30")

# Collect all busy intervals for each participant (in minutes)
busy_intervals = []

# Shirley: 10:30-11:00, 12:00-12:30 -> no overlap with [14:30, 17:00]
# Jacob: 14:30-15:00 -> becomes [870, 900]
busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("15:00"))  # Jacob

# Stephen: no interval in the window
# Margaret: 15:00-15:30, 16:30-17:00
busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("15:30")))  # Margaret
busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))  # Margaret

# Mason: 16:30-17:00
busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))  # Mason

# Filter and clip intervals to [effective_start, work_end]
filtered_intervals = []
for start, end in busy_intervals:
    if end > effective_start and start < work_end:
        clipped_start = max(start, effective_start)
        clipped_end = min(end, work_end)
        if clipped_start < clipped_end:
            filtered_intervals.append((clipped_start, clipped_end))

# Merge intervals
if not filtered_intervals:
    merged_intervals = []
else:
    filtered_intervals.sort(key=lambda x: x[0])
    merged_intervals = [filtered_intervals[0]]
    for interval in filtered_intervals[1:]:
        last = merged_intervals[-1]
        if interval[0] <= last[1]:
            merged_intervals[-1] = (last[0], max(last[1], interval[1]))
        else:
            merged_intervals.append(interval)

# Compute free intervals in [effective_start, work_end]
free_intervals = []
current = effective_start
for start, end in merged_intervals:
    if current < start:
        free_intervals.append((current, start))
    current = max(current, end)
if current < work_end:
    free_intervals.append((current, work_end))

# Find the first free interval with at least 30 minutes
meeting_duration = 30
meeting_start = None
for start, end in free_intervals:
    if end - start >= meeting_duration:
        meeting_start = start
        break

# If found, compute meeting end
if meeting_start is None:
    # According to the problem, a solution exists, so this should not happen
    meeting_time_str = "00:00:00:00"  # fallback
else:
    meeting_end = meeting_start + meeting_duration
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    meeting_time_str = f"{start_str}:{end_str}"

# Output day and meeting time range in braces
print("Monday")
print(f"{{{meeting_time_str}}}")