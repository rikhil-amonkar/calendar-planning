def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define parameters
day = "Monday"
meeting_duration = 30  # in minutes

# Albert's busy periods on Monday
albert_busy = [
    (9 * 60, 10 * 60),        # 9:00-10:00
    (10 * 60 + 30, 12 * 60),  # 10:30-12:00
    (15 * 60, 16 * 60 + 30)   # 15:00-16:30
]

# Albert's available time frame considering his constraints
available_start = 9 * 60     # 9:00 AM
available_end = 11 * 60      # 11:00 AM (he can't meet after this)

# Adjust busy periods to the available time frame
adjusted_busy = []
for start, end in albert_busy:
    busy_start = max(start, available_start)
    busy_end = min(end, available_end)
    if busy_start < busy_end:
        adjusted_busy.append((busy_start, busy_end))

# Sort adjusted busy periods by start time
adjusted_busy.sort(key=lambda x: x[0])

# Calculate free intervals within available time
free_intervals = []
current_free_start = available_start
for busy_start, busy_end in adjusted_busy:
    if current_free_start < busy_start:
        free_intervals.append((current_free_start, busy_start))
    current_free_start = max(current_free_start, busy_end)
# Check for remaining free time after last busy period
if current_free_start < available_end:
    free_intervals.append((current_free_start, available_end))

# Find the first suitable free interval
proposed_start = None
proposed_end = None
for start, end in free_intervals:
    if end - start >= meeting_duration:
        proposed_start = start
        proposed_end = start + meeting_duration
        break

# Output the result
if proposed_start is not None:
    time_range = f"{minutes_to_time(proposed_start)}:{minutes_to_time(proposed_end)}"
    print(f"Proposed time: {time_range} on {day}")
else:
    print("No suitable time found.")