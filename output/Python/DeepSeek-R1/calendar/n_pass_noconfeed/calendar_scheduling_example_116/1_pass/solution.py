def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

# Work hours: 9:00 to 17:00 (Monday)
work_start = 9 * 60   # 540 minutes (9:00)
work_end = 17 * 60    # 1020 minutes (17:00)

# Meeting duration
duration = 30

# Anna's preference: not before 14:30 (870 minutes)
anna_pref_start = 14 * 60 + 30

# Collect all busy intervals from every participant
busy_intervals = []

# Adam's schedule
busy_intervals.append((time_str_to_minutes("14:00"), time_str_to_minutes("15:00")))

# John's schedule
busy_intervals.append((time_str_to_minutes("13:00"), time_str_to_minutes("13:30")))
busy_intervals.append((time_str_to_minutes("14:00"), time_str_to_minutes("14:30")))
busy_intervals.append((time_str_to_minutes("15:30"), time_str_to_minutes("16:00")))
busy_intervals.append((time_str_to_minutes("16:30"), time_str_to_minutes("17:00")))

# Stephanie's schedule
busy_intervals.append((time_str_to_minutes("9:30"), time_str_to_minutes("10:00")))
busy_intervals.append((time_str_to_minutes("10:30"), time_str_to_minutes("11:00")))
busy_intervals.append((time_str_to_minutes("11:30"), time_str_to_minutes("16:00")))
busy_intervals.append((time_str_to_minutes("16:30"), time_str_to_minutes("17:00")))

# Anna's schedule
busy_intervals.append((time_str_to_minutes("9:30"), time_str_to_minutes("10:00")))
busy_intervals.append((time_str_to_minutes("12:00"), time_str_to_minutes("12:30")))
busy_intervals.append((time_str_to_minutes("13:00"), time_str_to_minutes("15:30")))
busy_intervals.append((time_str_to_minutes("16:30"), time_str_to_minutes("17:00")))

# Merge overlapping busy intervals
busy_intervals.sort(key=lambda x: x[0])
merged_busy = []
if busy_intervals:
    current_start, current_end = busy_intervals[0]
    for interval in busy_intervals[1:]:
        s, e = interval
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = s, e
    merged_busy.append((current_start, current_end))

# Compute free intervals within work hours
free_intervals = []
current = work_start
for s, e in merged_busy:
    if current < s:
        free_intervals.append((current, s))
    current = max(current, e)  # Ensure we move forward
if current < work_end:
    free_intervals.append((current, work_end))

# Find first free interval that fits meeting and Anna's preference
for start_free, end_free in free_intervals:
    candidate_start = max(start_free, anna_pref_start)
    if candidate_start + duration <= end_free:
        meeting_start = candidate_start
        meeting_end = candidate_start + duration
        break

# Format meeting time as HH:MM:HH:MM
s_hour = meeting_start // 60
s_min = meeting_start % 60
e_hour = meeting_end // 60
e_min = meeting_end % 60
time_range_str = f"{s_hour:02d}:{s_min:02d}:{e_hour:02d}:{e_min:02d}"

# Output the day and time range
print("Monday")
print(time_range_str)