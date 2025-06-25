def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Work hours
work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")

# Busy intervals
jeffrey_busy = [
    ("9:30", "10:00"),
    ("10:30", "11:00")
]
virginia_busy = [
    ("9:00", "9:30"),
    ("10:00", "10:30"),
    ("14:30", "15:00"),
    ("16:00", "16:30")
]
melissa_busy = [
    ("9:00", "11:30"),
    ("12:00", "12:30"),
    ("13:00", "15:00"),
    ("16:00", "17:00")
]

def convert_intervals(intervals):
    return [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

jeffrey_busy_min = convert_intervals(jeffrey_busy)
virginia_busy_min = convert_intervals(virginia_busy)
melissa_busy_min = convert_intervals(melissa_busy)

all_busy = jeffrey_busy_min + virginia_busy_min + melissa_busy_min
all_busy.sort(key=lambda x: x[0])

merged_busy = []
if all_busy:
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        s, e = all_busy[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = s, e
    merged_busy.append((current_start, current_end))

free_intervals = []
if not merged_busy:
    free_intervals.append((work_start, work_end))
else:
    if work_start < merged_busy[0][0]:
        free_intervals.append((work_start, merged_busy[0][0]))
    for i in range(len(merged_busy)-1):
        current_end = merged_busy[i][1]
        next_start = merged_busy[i+1][0]
        if current_end < next_start:
            free_intervals.append((current_end, next_start))
    if merged_busy[-1][1] < work_end:
        free_intervals.append((merged_busy[-1][1], work_end))

duration = 30
candidate_intervals = [(start, end) for start, end in free_intervals if end - start >= duration]

preferred_end_time = time_to_minutes("14:00")

chosen_interval = None
for interval in candidate_intervals:
    start, end = interval
    if end <= preferred_end_time:
        chosen_interval = interval
        break

if chosen_interval is None and candidate_intervals:
    chosen_interval = candidate_intervals[0]

if chosen_interval:
    start_min, end_min = chosen_interval
    meeting_start = start_min
    meeting_end = start_min + duration
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No suitable time found")