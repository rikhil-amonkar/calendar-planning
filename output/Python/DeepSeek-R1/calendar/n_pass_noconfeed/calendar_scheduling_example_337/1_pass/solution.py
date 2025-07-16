def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define work hours and meeting duration
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60    # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Initialize events list
events = []

# John's meetings
events.append((time_to_minutes("11:30"), 1))
events.append((time_to_minutes("12:00"), -1))
events.append((time_to_minutes("14:00"), 1))
events.append((time_to_minutes("14:30"), -1))

# Megan's meetings
events.append((time_to_minutes("12:00"), 1))
events.append((time_to_minutes("12:30"), -1))
events.append((time_to_minutes("14:00"), 1))
events.append((time_to_minutes("15:00"), -1))
events.append((time_to_minutes("15:30"), 1))
events.append((time_to_minutes("16:00"), -1))

# Brandon has no meetings

# Kimberly's meetings
events.append((time_to_minutes("9:00"), 1))
events.append((time_to_minutes("9:30"), -1))
events.append((time_to_minutes("10:00"), 1))
events.append((time_to_minutes("10:30"), -1))
events.append((time_to_minutes("11:00"), 1))
events.append((time_to_minutes("14:30"), -1))
events.append((time_to_minutes("15:00"), 1))
events.append((time_to_minutes("16:00"), -1))
events.append((time_to_minutes("16:30"), 1))
events.append((time_to_minutes("17:00"), -1))

# Sean's meetings
events.append((time_to_minutes("10:00"), 1))
events.append((time_to_minutes("11:00"), -1))
events.append((time_to_minutes("11:30"), 1))
events.append((time_to_minutes("14:00"), -1))
events.append((time_to_minutes("15:00"), 1))
events.append((time_to_minutes("15:30"), -1))

# Lori's meetings
events.append((time_to_minutes("9:00"), 1))
events.append((time_to_minutes("9:30"), -1))
events.append((time_to_minutes("10:30"), 1))
events.append((time_to_minutes("12:00"), -1))
events.append((time_to_minutes("13:00"), 1))
events.append((time_to_minutes("14:30"), -1))
events.append((time_to_minutes("16:00"), 1))
events.append((time_to_minutes("16:30"), -1))

# Sort events by time and then by delta (end events before start events at same time)
events.sort(key=lambda x: (x[0], x[1]))

# Compute free intervals
current_counter = 0
current_start = work_start
free_intervals = []

for time, delta in events:
    if time > work_end:
        continue
    if current_counter == 0 and current_start < time:
        free_intervals.append((current_start, time))
    current_counter += delta
    if current_counter == 0:
        current_start = time

if current_counter == 0 and current_start < work_end:
    free_intervals.append((current_start, work_end))

# Find the first free interval that can fit the meeting
meeting_start = None
for start, end in free_intervals:
    if end - start >= meeting_duration:
        meeting_start = start
        break

# Convert meeting start and end to time strings
meeting_end = meeting_start + meeting_duration
start_str = minutes_to_time(meeting_start)
end_str = minutes_to_time(meeting_end)

# Output the day and time range
print("Monday")
print(f"{start_str}:{end_str}")