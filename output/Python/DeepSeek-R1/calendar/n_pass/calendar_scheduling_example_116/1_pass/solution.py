def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours
work_start = time_to_minutes("9:00")  # 540 minutes
work_end = time_to_minutes("17:00")   # 1020 minutes

# Collect all busy intervals (as half-open [start, end))
busy_intervals = []

# Adam: 14:00 to 15:00
busy_intervals.append([time_to_minutes("14:00"), time_to_minutes("15:00")])

# John
busy_intervals.append([time_to_minutes("13:00"), time_to_minutes("13:30")])
busy_intervals.append([time_to_minutes("14:00"), time_to_minutes("14:30")])
busy_intervals.append([time_to_minutes("15:30"), time_to_minutes("16:00")])
busy_intervals.append([time_to_minutes("16:30"), time_to_minutes("17:00")])

# Stephanie
busy_intervals.append([time_to_minutes("9:30"), time_to_minutes("10:00")])
busy_intervals.append([time_to_minutes("10:30"), time_to_minutes("11:00")])
busy_intervals.append([time_to_minutes("11:30"), time_to_minutes("16:00")])
busy_intervals.append([time_to_minutes("16:30"), time_to_minutes("17:00")])

# Anna
busy_intervals.append([time_to_minutes("9:30"), time_to_minutes("10:00")])
busy_intervals.append([time_to_minutes("12:00"), time_to_minutes("12:30")])
busy_intervals.append([time_to_minutes("13:00"), time_to_minutes("15:30")])
busy_intervals.append([time_to_minutes("16:30"), time_to_minutes("17:00")])

# Merge busy intervals
busy_intervals.sort(key=lambda x: x[0])
merged_busy = []
current_start, current_end = busy_intervals[0]
for i in range(1, len(busy_intervals)):
    s, e = busy_intervals[i]
    if s <= current_end:
        current_end = max(current_end, e)
    else:
        merged_busy.append([current_start, current_end])
        current_start, current_end = s, e
merged_busy.append([current_start, current_end])

# Compute free intervals within work hours
free_intervals = []
prev_end = work_start
for start, end in merged_busy:
    if prev_end < start:
        free_intervals.append([prev_end, start])
    prev_end = end
if prev_end < work_end:
    free_intervals.append([prev_end, work_end])

# Anna's preference: not before 14:30 (870 minutes)
anna_pref_min = time_to_minutes("14:30")
meeting_duration = 30

# Find the first free interval that can accommodate the meeting after 14:30
meeting_start = None
for start, end in free_intervals:
    candidate_start = max(start, anna_pref_min)
    if candidate_start + meeting_duration <= end:
        meeting_start = candidate_start
        break

# Convert meeting start and end times
meeting_end = meeting_start + meeting_duration
start_time_str = minutes_to_time(meeting_start)
end_time_str = minutes_to_time(meeting_end)

# Output day and time in the required format
print("Monday")
print(f"{start_time_str}:{end_time_str}")