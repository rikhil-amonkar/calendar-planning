def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Work hours
work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")

# Meeting duration
duration = 30

# Roger's preference: not before 12:30
preference_start = time_to_minutes("12:30")
start_search = max(work_start, preference_start)
end_search = work_end

# Busy times for each participant
busy_times = {
    "Daniel": [],
    "Kathleen": [("14:30", "15:30")],
    "Carolyn": [("12:00", "12:30"), ("13:00", "13:30")],
    "Roger": [],
    "Cheryl": [("9:00", "9:30"), ("10:00", "11:30"), ("12:30", "13:30"), ("14:00", "17:00")],
    "Virginia": [("9:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Angela": [("9:30", "10:00"), ("10:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")]
}

# Collect all busy intervals that overlap with [start_search, end_search]
all_busy = []
for person, intervals in busy_times.items():
    for interval in intervals:
        start_str, end_str = interval
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        if end_min <= start_search or start_min >= end_search:
            continue
        start_busy = max(start_min, start_search)
        end_busy = min(end_min, end_search)
        if start_busy < end_busy:
            all_busy.append((start_busy, end_busy))

# Sort intervals by start time
all_busy.sort(key=lambda x: x[0])

# Merge intervals
merged_busy = []
if all_busy:
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        start, end = all_busy[i]
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = start, end
    merged_busy.append((current_start, current_end))
else:
    merged_busy = []

# Find free slots
free_slots = []
current_time = start_search
for busy_start, busy_end in merged_busy:
    if current_time < busy_start:
        free_slots.append((current_time, busy_start))
    current_time = busy_end
if current_time < end_search:
    free_slots.append((current_time, end_search))

# Find a slot with sufficient duration
for slot in free_slots:
    start, end = slot
    if end - start >= duration:
        meeting_start = start
        meeting_end = start + duration
        time_range = minutes_to_time(meeting_start) + ":" + minutes_to_time(meeting_end)
        print("Monday")
        print(time_range)
        break
else:
    print("No suitable time found")