# Define work hours and meeting duration
day_start_minutes = 0    # 9:00
day_end_minutes = 480    # 17:00 (8 hours after 9:00)
duration = 30
constraint_start = 300   # 14:00 (5 hours after 9:00)

# Collect all busy intervals (including constraint)
busy_intervals = []

# Add constraint: [0, 300) - no meetings before 14:00
busy_intervals.append((0, constraint_start))

# David's busy times
busy_intervals.append((150, 180))  # 11:30-12:00
busy_intervals.append((330, 360))  # 14:30-15:00

# Douglas' busy times
busy_intervals.append((30, 60))    # 9:30-10:00
busy_intervals.append((150, 180))  # 11:30-12:00
busy_intervals.append((240, 270))  # 13:00-13:30
busy_intervals.append((330, 360))  # 14:30-15:00

# Ralph's busy times
busy_intervals.append((0, 30))     # 9:00-9:30
busy_intervals.append((60, 120))   # 10:00-11:00
busy_intervals.append((150, 210))  # 11:30-12:30
busy_intervals.append((270, 360))  # 13:30-15:00
busy_intervals.append((390, 420))  # 15:30-16:00
busy_intervals.append((450, 480))  # 16:30-17:00

# Jordan's busy times
busy_intervals.append((0, 60))     # 9:00-10:00
busy_intervals.append((180, 210))  # 12:00-12:30
busy_intervals.append((240, 270))  # 13:00-13:30
busy_intervals.append((330, 360))  # 14:30-15:00
busy_intervals.append((390, 480))  # 15:30-17:00

# Merge intervals
sorted_intervals = sorted(busy_intervals, key=lambda x: x[0])
merged = []
start, end = sorted_intervals[0]
for interval in sorted_intervals[1:]:
    s, e = interval
    if s <= end:
        end = max(end, e)
    else:
        merged.append((start, end))
        start, end = s, e
merged.append((start, end))

# Find first available gap after constraint_start
free_start = constraint_start
meeting_time = None
for s, e in merged:
    if s > free_start:
        if s - free_start >= duration:
            meeting_time = (free_start, free_start + duration)
            break
    if e > free_start:
        free_start = e
if meeting_time is None and day_end_minutes - free_start >= duration:
    meeting_time = (free_start, free_start + duration)

# Convert meeting time to HH:MM format
start_minutes, end_minutes = meeting_time
start_hour = 9 + start_minutes // 60
start_min = start_minutes % 60
end_hour = 9 + end_minutes // 60
end_min = end_minutes % 60

start_str = f"{int(start_hour):02d}:{int(start_min):02d}"
end_str = f"{int(end_hour):02d}:{int(end_min):02d}"
time_output = f"{start_str}:{end_str}"

# Output results
print("Monday")
print(time_output)