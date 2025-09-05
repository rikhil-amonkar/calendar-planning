def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting requirements
meeting_duration = 30  # duration in minutes
working_start = 9 * 60     # 9:00 in minutes
working_end = 17 * 60      # 17:00 in minutes

# Busy intervals (in minutes) for each participant on Monday
busy_intervals = [
    # Patrick: 9:00-9:30, 10:00-10:30, 13:30-14:00, 16:00-16:30
    (9 * 60, 9 * 60 + 30),
    (10 * 60, 10 * 60 + 30),
    (13 * 60 + 30, 14 * 60),
    (16 * 60, 16 * 60 + 30),
    # Kayla: 12:30-13:30, 15:00-15:30, 16:00-16:30
    (12 * 60 + 30, 13 * 60 + 30),
    (15 * 60, 15 * 60 + 30),
    (16 * 60, 16 * 60 + 30),
    # Carl: 10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-17:00
    (10 * 60 + 30, 11 * 60),
    (12 * 60, 12 * 60 + 30),
    (13 * 60, 13 * 60 + 30),
    (14 * 60 + 30, 17 * 60),
    # Christian: 9:00-12:30, 13:00-14:00, 14:30-17:00
    (9 * 60, 12 * 60 + 30),
    (13 * 60, 14 * 60),
    (14 * 60 + 30, 17 * 60)
]

# Sort the busy intervals by their start times
busy_intervals.sort(key=lambda interval: interval[0])

# Merge overlapping busy intervals
merged_busy = []
for interval in busy_intervals:
    if not merged_busy:
        merged_busy.append(interval)
    else:
        last_start, last_end = merged_busy[-1]
        current_start, current_end = interval
        if current_start <= last_end:  # overlapping or contiguous intervals
            merged_busy[-1] = (last_start, max(last_end, current_end))
        else:
            merged_busy.append(interval)

# Find free slots within working hours
free_slots = []

# Check time before the first busy interval
if working_start < merged_busy[0][0]:
    if merged_busy[0][0] - working_start >= meeting_duration:
        free_slots.append((working_start, merged_busy[0][0]))

# Check gaps between busy intervals
for i in range(len(merged_busy) - 1):
    gap_start = merged_busy[i][1]
    gap_end = merged_busy[i + 1][0]
    if gap_end - gap_start >= meeting_duration:
        free_slots.append((gap_start, gap_end))

# Check time after the last busy interval
if merged_busy[-1][1] < working_end:
    if working_end - merged_busy[-1][1] >= meeting_duration:
        free_slots.append((merged_busy[-1][1], working_end))

# Choose the first free slot that can accommodate the meeting duration
meeting_start = None
meeting_end = None
for slot in free_slots:
    start, end = slot
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

# Output the meeting time and day of the week
if meeting_start is not None:
    meeting_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    meeting_day = "Monday"
    print(f"Day: {meeting_day}")
    print(f"Time: {meeting_time}")
else:
    print("No available slot found.")