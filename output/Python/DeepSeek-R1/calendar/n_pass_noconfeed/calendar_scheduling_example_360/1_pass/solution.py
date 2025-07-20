def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    mins = total_minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work day in minutes (relative to 9:00)
work_start = 0
work_end = 480  # 17:00 is 8 hours after 9:00

# Collect all busy intervals (in minutes relative to 9:00)
busy_intervals = []

# Emily's meetings
busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("10:30")))
busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("16:30")))

# Maria's meetings
busy_intervals.append((time_to_minutes("10:30"), time_to_minutes("11:00")))
busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("14:30")))

# Carl's meetings
busy_intervals.append((time_to_minutes("9:30"), time_to_minutes("10:00")))
busy_intervals.append((time_to_minutes("10:30"), time_to_minutes("12:30")))
busy_intervals.append((time_to_minutes("13:30"), time_to_minutes("14:00")))
busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("15:30")))
busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("17:00")))

# David's meetings
busy_intervals.append((time_to_minutes("9:30"), time_to_minutes("11:00")))
busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("12:00")))
busy_intervals.append((time_to_minutes("12:30"), time_to_minutes("13:30")))
busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("15:00")))
busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("17:00")))

# Frank's meetings
busy_intervals.append((time_to_minutes("9:30"), time_to_minutes("10:30")))
busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
busy_intervals.append((time_to_minutes("12:30"), time_to_minutes("13:30")))
busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("17:00")))

# Mason has no meetings

# Sort intervals by start time
busy_intervals.sort(key=lambda x: x[0])

# Merge intervals
if not busy_intervals:
    merged = []
else:
    merged = []
    current_start, current_end = busy_intervals[0]
    for s, e in busy_intervals[1:]:
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))

# Compute free intervals
free_intervals = []
prev_end = work_start
for start, end in merged:
    if prev_end < start:
        free_intervals.append((prev_end, start))
    prev_end = end
if prev_end < work_end:
    free_intervals.append((prev_end, work_end))

# Find the first free interval that can fit 30 minutes
meeting_duration = 30
proposed_start = None
for start, end in free_intervals:
    if end - start >= meeting_duration:
        proposed_start = start
        break

# Convert to time strings
start_time_str = minutes_to_time(proposed_start)
end_time_str = minutes_to_time(proposed_start + meeting_duration)

# Format output as HH:MM:HH:MM
start_hour, start_min = start_time_str.split(':')
end_hour, end_min = end_time_str.split(':')
time_output = f"{start_hour}:{start_min}:{end_hour}:{end_min}"

# Output day and time
print("Monday")
print(time_output)