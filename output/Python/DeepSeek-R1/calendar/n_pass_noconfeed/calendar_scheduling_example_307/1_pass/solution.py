work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60   # 17:00 in minutes

# List to collect all busy intervals
busy_intervals = []

# Stephen's busy times
busy_intervals.append((10 * 60, 10 * 60 + 30))  # 10:00-10:30
busy_intervals.append((12 * 60, 12 * 60 + 30))  # 12:00-12:30

# Brittany's busy times
busy_intervals.append((11 * 60, 11 * 60 + 30))      # 11:00-11:30
busy_intervals.append((13 * 60 + 30, 14 * 60))      # 13:30-14:00
busy_intervals.append((15 * 60 + 30, 16 * 60))      # 15:30-16:00
busy_intervals.append((16 * 60 + 30, 17 * 60))      # 16:30-17:00

# Dorothy's busy times
busy_intervals.append((9 * 60, 9 * 60 + 30))        # 9:00-9:30
busy_intervals.append((10 * 60, 10 * 60 + 30))      # 10:00-10:30
busy_intervals.append((11 * 60, 12 * 60 + 30))      # 11:00-12:30
busy_intervals.append((13 * 60, 15 * 60))           # 13:00-15:00
busy_intervals.append((15 * 60 + 30, 17 * 60))      # 15:30-17:00

# Rebecca's busy times
busy_intervals.append((9 * 60 + 30, 10 * 60 + 30))  # 9:30-10:30
busy_intervals.append((11 * 60, 11 * 60 + 30))      # 11:00-11:30
busy_intervals.append((12 * 60, 12 * 60 + 30))      # 12:00-12:30
busy_intervals.append((13 * 60, 17 * 60))           # 13:00-17:00

# Jordan's busy times
busy_intervals.append((9 * 60, 9 * 60 + 30))        # 9:00-9:30
busy_intervals.append((10 * 60, 11 * 60))            # 10:00-11:00
busy_intervals.append((11 * 60 + 30, 12 * 60))      # 11:30-12:00
busy_intervals.append((13 * 60, 15 * 60))            # 13:00-15:00
busy_intervals.append((15 * 60 + 30, 16 * 60 + 30)) # 15:30-16:30

# Sort the busy intervals by start time
busy_intervals.sort(key=lambda x: x[0])

# Merge overlapping or adjacent intervals
merged = []
if busy_intervals:
    current_start, current_end = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        interval = busy_intervals[i]
        if interval[0] <= current_end:
            current_end = max(current_end, interval[1])
        else:
            merged.append((current_start, current_end))
            current_start, current_end = interval
    merged.append((current_start, current_end))

# Find free intervals within work hours
free_intervals = []
if not merged:
    free_intervals.append((work_start, work_end))
else:
    # Check before the first busy interval
    if work_start < merged[0][0]:
        free_intervals.append((work_start, merged[0][0]))
    
    # Check between busy intervals
    for i in range(1, len(merged)):
        prev_end = merged[i-1][1]
        curr_start = merged[i][0]
        if prev_end < curr_start:
            free_intervals.append((prev_end, curr_start))
    
    # Check after the last busy interval
    if merged[-1][1] < work_end:
        free_intervals.append((merged[-1][1], work_end))

# Find the first free interval that can fit the 30-minute meeting
meeting_start = None
for start, end in free_intervals:
    if end - start >= 30:
        meeting_start = start
        break

# If a suitable slot is found, convert to time strings
if meeting_start is not None:
    meeting_end = meeting_start + 30
    
    # Convert start time to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    start_str = f"{start_hour}:{start_minute:02d}"
    
    # Convert end time to HH:MM format
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60
    end_str = f"{end_hour}:{end_minute:02d}"
    
    # Format the time range as HH:MM:HH:MM
    time_range_str = f"{start_str}:{end_str}"
    
    # Output the day and time range
    print("Monday")
    print(time_range_str)
else:
    # According to the problem, there is a solution, so this should not happen.
    print("No suitable time found")