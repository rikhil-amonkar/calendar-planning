def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define the day and work hours
day = "Monday"
work_start = "9:00"
work_end = "17:00"

# Busy times for each participant
busy_times = {
    "Gregory": [("9:00", "10:00"), ("10:30", "11:30"), ("12:30", "13:00"), ("13:30", "14:00")],
    "Natalie": [],
    "Christine": [("9:00", "11:30"), ("13:30", "17:00")],
    "Vincent": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")],
}

# Convert work hours to minutes
day_start = time_to_minutes(work_start)
day_end = time_to_minutes(work_end)

# Collect all busy intervals in minutes
all_busy = []
for intervals in busy_times.values():
    for interval in intervals:
        start_min = time_to_minutes(interval[0])
        end_min = time_to_minutes(interval[1])
        all_busy.append((start_min, end_min))

# Merge busy intervals
if not all_busy:
    merged_busy = []
else:
    all_busy.sort(key=lambda x: x[0])
    merged_busy = []
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        s, e = all_busy[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = s, e
    merged_busy.append((current_start, current_end))

# Find free intervals within work hours
free_intervals = []
current = day_start
for start, end in merged_busy:
    if current < start:
        free_intervals.append((current, start))
    current = max(current, end)
if current < day_end:
    free_intervals.append((current, day_end))

# Find first free interval that fits 30-minute meeting
meeting_duration = 30
meeting_start = None
for start, end in free_intervals:
    if end - start >= meeting_duration:
        meeting_start = start
        break

# Output result
meeting_end = meeting_start + meeting_duration
start_str = minutes_to_time(meeting_start)
end_str = minutes_to_time(meeting_end)
time_range_str = f"{start_str}:{end_str}"
print(day)
print(time_range_str)