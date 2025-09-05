def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours and meeting duration (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Samuel's busy intervals on Monday (in HH:MM format)
busy_intervals_str = [
    ("09:00", "10:30"),
    ("11:30", "12:00"),
    ("13:00", "13:30"),
    ("14:00", "16:00"),
    ("16:30", "17:00")
]

# Convert busy intervals to minutes
busy_intervals = [(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_intervals_str]

# Sort intervals by start time (Andrew and Grace are free all day, so only Samuel's intervals matter)
busy_intervals.sort()

# Start from the beginning of the work day
current_time = work_start
meeting_start = None

# Find earliest gap large enough for the meeting
for start, end in busy_intervals:
    if start - current_time >= meeting_duration:
        meeting_start = current_time
        break
    else:
        # Move current time forward if it is within a busy window
        current_time = max(current_time, end)

# If no gap was found within the busy intervals, check after the last meeting
if meeting_start is None and work_end - current_time >= meeting_duration:
    meeting_start = current_time

# Calculate meeting end time
meeting_end = meeting_start + meeting_duration

# Day of the meeting
day = "Monday"

# Output in format HH:MM:HH:MM along with the day of week
print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} {day}")