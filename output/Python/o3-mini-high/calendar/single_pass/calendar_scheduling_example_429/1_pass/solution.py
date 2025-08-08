def time_to_minutes(ts):
    hours, minutes = map(int, ts.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Working hours on Monday (09:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Busy intervals for each participant (start, end) in minutes
busy_intervals = [
    # Judy
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30")),
    # Olivia
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    # Jacqueline
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    # Laura
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00")),
    # Tyler
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("17:00")),
    # Lisa
    (time_to_minutes("09:30"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Sort the intervals by start time
busy_intervals.sort(key=lambda interval: interval[0])

# Merge overlapping or contiguous busy intervals
merged_busy = []
for interval in busy_intervals:
    if not merged_busy:
        merged_busy.append(interval)
    else:
        last_start, last_end = merged_busy[-1]
        current_start, current_end = interval
        if current_start <= last_end:  # Overlapping or touching intervals
            merged_busy[-1] = (last_start, max(last_end, current_end))
        else:
            merged_busy.append(interval)

# Determine free intervals within the working period
free_intervals = []
current_time = work_start

for interval in merged_busy:
    busy_start, busy_end = interval
    if busy_start > current_time:
        free_intervals.append((current_time, busy_start))
    current_time = max(current_time, busy_end)
if current_time < work_end:
    free_intervals.append((current_time, work_end))

# Find the first free interval that can accommodate the meeting
meeting_slot = None
for free in free_intervals:
    free_start, free_end = free
    if free_end - free_start >= meeting_duration:
        meeting_slot = (free_start, free_start + meeting_duration)
        break

if meeting_slot:
    meeting_start = minutes_to_time(meeting_slot[0])
    meeting_end = minutes_to_time(meeting_slot[1])
    print("Monday")
    print(f"{meeting_start}:{meeting_end}")
else:
    print("No available time slot found for the meeting.")