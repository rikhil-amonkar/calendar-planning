def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def minutes_to_time(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

# List of busy intervals for each participant
anthony_intervals = ["9:30-10:00", "12:00-13:00", "16:00-16:30"]
pamela_intervals = ["9:30-10:00", "16:30-17:00"]
# Add Pamela's constraint: unavailable after 14:30
pamela_intervals.append("14:30-17:00")
zachary_intervals = ["9:00-11:30", "12:00-12:30", "13:00-13:30", "14:30-15:00", "16:00-17:00"]

busy_intervals = []

# Parse and add Anthony's intervals
for interval in anthony_intervals:
    start_str, end_str = interval.split('-')
    start_min = time_str_to_minutes(start_str)
    end_min = time_str_to_minutes(end_str)
    busy_intervals.append((start_min, end_min))

# Parse and add Pamela's intervals
for interval in pamela_intervals:
    start_str, end_str = interval.split('-')
    start_min = time_str_to_minutes(start_str)
    end_min = time_str_to_minutes(end_str)
    busy_intervals.append((start_min, end_min))

# Parse and add Zachary's intervals
for interval in zachary_intervals:
    start_str, end_str = interval.split('-')
    start_min = time_str_to_minutes(start_str)
    end_min = time_str_to_minutes(end_str)
    busy_intervals.append((start_min, end_min))

# Sort busy_intervals by start time
busy_intervals.sort(key=lambda x: x[0])

# Merge overlapping intervals
merged_busy = []
if busy_intervals:
    current_start, current_end = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        interval = busy_intervals[i]
        if interval[0] <= current_end:
            current_end = max(current_end, interval[1])
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = interval
    merged_busy.append((current_start, current_end))

# Find free intervals between 0 and 480 (work hours)
free_intervals = []
start = 0
for interval in merged_busy:
    if start < interval[0]:
        free_intervals.append((start, interval[0]))
    start = max(start, interval[1])
if start < 480:
    free_intervals.append((start, 480))

# Find the first free interval that fits a 60-minute meeting
meeting_duration = 60
meeting_interval = None
for free in free_intervals:
    if free[1] - free[0] >= meeting_duration:
        meeting_start = free[0]
        meeting_end = meeting_start + meeting_duration
        meeting_interval = (meeting_start, meeting_end)
        break

# Convert meeting times to HH:MM format and output
if meeting_interval:
    start_min, end_min = meeting_interval
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(end_min)
    # Format as HH:MM:HH:MM
    start_hour, start_minute = start_time.split(':')
    end_hour, end_minute = end_time.split(':')
    time_str = f"{start_hour}:{start_minute}:{end_hour}:{end_minute}"
    print("Monday")
    print(time_str)
else:
    print("No suitable time found")