def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(mins):
    hour = mins // 60
    minute = mins % 60
    return f"{hour:02d}:{minute:02d}"

# Define work hours
work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")

# Collect all busy intervals
busy_intervals = []

# John's meetings
busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("12:00")))
busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("14:30")))

# Megan's meetings
busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("12:30")))
busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("15:00")))
busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("16:00")))

# Kimberly's meetings
busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("9:30")))
busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("10:30")))
busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("14:30")))
busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("16:00")))
busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))

# Sean's meetings
busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("11:00")))
busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("14:00")))
busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("15:30")))

# Lori's meetings
busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("9:30")))
busy_intervals.append((time_to_minutes("10:30"), time_to_minutes("12:00")))
busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("14:30")))
busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("16:30")))

# Sort busy intervals by start time
busy_intervals.sort(key=lambda x: x[0])

# Merge overlapping intervals
merged = []
for interval in busy_intervals:
    if not merged:
        merged.append(interval)
    else:
        last_start, last_end = merged[-1]
        current_start, current_end = interval
        if current_start <= last_end:
            merged[-1] = (last_start, max(last_end, current_end))
        else:
            merged.append(interval)

# Compute free intervals
free_intervals = []
current_start = work_start

for start, end in merged:
    if current_start < start:
        free_intervals.append((current_start, start))
    current_start = max(current_start, end)
    
if current_start < work_end:
    free_intervals.append((current_start, work_end))

# Find first free interval of at least 30 minutes
meeting_time = None
for start, end in free_intervals:
    if end - start >= 30:
        meeting_time = (start, start + 30)
        break

# Format output
start_min, end_min = meeting_time
time_range_str = f"{minutes_to_time(start_min)}:{minutes_to_time(end_min)}"
day = "Monday"

print(time_range_str)
print(day)