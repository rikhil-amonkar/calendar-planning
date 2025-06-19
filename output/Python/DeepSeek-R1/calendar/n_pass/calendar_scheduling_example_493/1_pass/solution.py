work_start = 0  # 9:00 in minutes from 9:00
work_end = 480  # 17:00

# Define all busy intervals (each as tuple (start, end))
busy_intervals = [
    # Stephanie
    (120, 150),
    (330, 360),
    # Joe
    (0, 30),
    (60, 180),
    (210, 240),
    (300, 480),
    # Diana
    (0, 90),
    (150, 180),
    (240, 300),
    (330, 390),
    (420, 480),
    # Deborah
    (0, 60),
    (90, 180),
    (210, 240),
    (270, 300),
    (330, 390),
    (420, 450)
]

# Sort and merge intervals
busy_intervals_sorted = sorted(busy_intervals, key=lambda x: x[0])
merged = []
for s, e in busy_intervals_sorted:
    if merged and s <= merged[-1][1]:
        if e > merged[-1][1]:
            merged[-1][1] = e
    else:
        merged.append([s, e])

# Calculate free intervals
free_intervals = []
current = work_start
for interval in merged:
    s, e = interval
    if current < s:
        free_intervals.append((current, s))
    current = e
if current < work_end:
    free_intervals.append((current, work_end))

# Find the first free interval with at least 30 minutes
meeting_start = None
for s, e in free_intervals:
    if e - s >= 30:
        meeting_start = s
        break

# Convert meeting_start to time string
total_minutes_start = meeting_start
hour_start = 9 + total_minutes_start // 60
minute_start = total_minutes_start % 60
meeting_end_minutes = meeting_start + 30
hour_end = 9 + meeting_end_minutes // 60
minute_end = meeting_end_minutes % 60

# Format to HH:MM
time_str = f"{hour_start:02d}:{minute_start:02d}:{hour_end:02d}:{minute_end:02d}"

print("Monday")
print(time_str)