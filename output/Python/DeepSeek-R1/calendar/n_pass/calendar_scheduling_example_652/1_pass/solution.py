def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define work hours for Tuesday (9:00 to 16:30) in minutes
work_start = 9 * 60   # 540 minutes (9:00)
work_end = 16 * 60 + 30  # 990 minutes (16:30)

# Busy intervals for Jesse on Tuesday (in minutes)
jesse_busy = [
    [9*60, 9*60+30],    # 9:00-9:30
    [13*60, 13*60+30],  # 13:00-13:30
    [14*60, 15*60]      # 14:00-15:00
]

# Busy intervals for Lawrence on Tuesday (in minutes)
lawrence_busy = [
    [9*60+30, 10*60+30],  # 9:30-10:30
    [11*60+30, 12*60+30], # 11:30-12:30
    [13*60, 13*60+30],    # 13:00-13:30
    [14*60+30, 15*60],    # 14:30-15:00
    [15*60+30, 16*60+30]  # 15:30-16:30
]

# Combine and sort all busy intervals by start time
all_busy = jesse_busy + lawrence_busy
all_busy.sort(key=lambda x: x[0])

# Merge overlapping busy intervals
merged_busy = []
current_start, current_end = all_busy[0]
for interval in all_busy[1:]:
    if interval[0] <= current_end:
        current_end = max(current_end, interval[1])
    else:
        merged_busy.append([current_start, current_end])
        current_start, current_end = interval
merged_busy.append([current_start, current_end])

# Compute free intervals within work hours
free_intervals = []
current = work_start
for start, end in merged_busy:
    if current < start:
        free_intervals.append([current, start])
    current = max(current, end)
if current < work_end:
    free_intervals.append([current, work_end])

# Find the first free interval with at least 30 minutes
meeting_start = None
for start, end in free_intervals:
    if end - start >= 30:
        meeting_start = start
        break

# If found, schedule meeting from meeting_start to meeting_start+30
if meeting_start is not None:
    meeting_end = meeting_start + 30
    start_str = min_to_time(meeting_start)
    end_str = min_to_time(meeting_end)
    print(f"Tuesday {start_str}:{end_str}")
else:
    # According to the problem, a solution exists
    print("No suitable time found")