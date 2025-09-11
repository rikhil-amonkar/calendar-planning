def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

# Define participants' busy times
participants = {
    'Jacob': [(13*60+30, 14*60+0), (14*60+30, 15*60+0)],
    'Diana': [(9*60+30, 10*60+0), (11*60+30, 12*60+0), (13*60+0, 13*60+30), (16*60+0, 16*60+30)],
    'Adam': [(9*60+30, 10*60+30), (11*60+0, 12*60+30), (15*60+30, 16*60+0)],
    'Angela': [(9*60+30, 10*60+0), (10*60+30, 12*60+0), (13*60+0, 15*60+30), (16*60+0, 16*60+30)],
    'Dennis': [(9*60+0, 9*60+30), (10*60+30, 11*60+30), (13*60+0, 15*60+0), (16*60+30, 17*60+0)],
}

# Collect all intervals
all_intervals = []
for busy_list in participants.values():
    all_intervals.extend(busy_list)

# Merge intervals
merged = merge_intervals(all_intervals)

# Work hours
work_start = 9 * 60  # 540
work_end = 17 * 60   # 1020

# Compute free intervals
free_intervals = []
prev_end = work_start
for interval in merged:
    start, end = interval
    if prev_end < start:
        free_intervals.append((prev_end, start))
    prev_end = max(prev_end, end)
# Check after the last interval
if prev_end < work_end:
    free_intervals.append((prev_end, work_end))

# Find suitable free time
for free_start, free_end in free_intervals:
    duration = free_end - free_start
    if duration >= 30:
        # Take the first 30 minutes
        meeting_start = free_start
        meeting_end = meeting_start + 30
        break

# Output
time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
day = "Monday"
print(f"{time_str} {day}")