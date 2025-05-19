from datetime import time, datetime, timedelta

def parse_time(t_str):
    return datetime.strptime(t_str, "%H:%M").time()

def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    return time(hour=m // 60, minute=m % 60)

participants = {
    "Joshua": [
        ("11:00", "12:30"),
        ("13:30", "14:30"),
        ("16:30", "17:00")
    ],
    "Jerry": [
        ("09:00", "09:30"),
        ("10:30", "12:00"),
        ("12:30", "13:00"),
        ("13:30", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "16:00")
    ],
    "Jesse": [
        ("09:00", "09:30"),
        ("10:30", "12:00"),
        ("12:30", "13:00"),
        ("14:30", "15:00"),
        ("15:30", "16:30")
    ],
    "Kenneth": [
        ("10:30", "12:30"),
        ("13:30", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
}

work_start = time_to_minutes(parse_time("09:00"))
work_end = time_to_minutes(parse_time("17:00"))

# Collect all busy intervals
busy_intervals = []
for person, intervals in participants.items():
    for start, end in intervals:
        s = time_to_minutes(parse_time(start))
        e = time_to_minutes(parse_time(end))
        busy_intervals.append((s, e))

# Sort intervals by start time
busy_intervals.sort()

# Merge overlapping intervals
merged = []
for start, end in busy_intervals:
    if not merged:
        merged.append((start, end))
    else:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))

# Find available slots
available = []
prev_end = work_start
for start, end in merged:
    if start > prev_end:
        available.append((prev_end, start))
    prev_end = max(prev_end, end)
if prev_end < work_end:
    available.append((prev_end, work_end))

# Find first available slot with >=60 minutes duration
meeting_duration = 60
for slot in available:
    start_min, end_min = slot
    if end_min - start_min >= meeting_duration:
        best_start = start_min
        best_end = start_min + meeting_duration
        break

# Format output
start_time = minutes_to_time(best_start)
end_time = minutes_to_time(best_end)
print(f"Monday {start_time.hour:02d}:{start_time.minute:02d}:{end_time.hour:02d}:{end_time.minute:02d}")