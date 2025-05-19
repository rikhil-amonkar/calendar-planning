from datetime import time, timedelta, datetime

# Define a helper function to convert hours and minutes to minutes from midnight
def hm_to_minutes(h, m):
    return h * 60 + m

# Helper function to convert minutes into HH:MM format string
def minutes_to_hm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Working day start and end in minutes (9:00 to 17:00)
work_start = hm_to_minutes(9, 0)
work_end = hm_to_minutes(17, 0)

# Meeting duration in minutes
meeting_duration = 30

# Define the busy schedules (in minutes) for each participant on Monday
# Format: (start, end) where start and end are minutes from midnight.
busy_intervals = [
    # Patrick's busy intervals
    (hm_to_minutes(9, 0), hm_to_minutes(9, 30)),
    (hm_to_minutes(10, 0), hm_to_minutes(10, 30)),
    (hm_to_minutes(13, 30), hm_to_minutes(14, 0)),
    (hm_to_minutes(16, 0), hm_to_minutes(16, 30)),
    
    # Kayla's busy intervals
    (hm_to_minutes(12, 30), hm_to_minutes(13, 30)),
    (hm_to_minutes(15, 0), hm_to_minutes(15, 30)),
    (hm_to_minutes(16, 0), hm_to_minutes(16, 30)),
    
    # Carl's busy intervals
    (hm_to_minutes(10, 30), hm_to_minutes(11, 0)),
    (hm_to_minutes(12, 0), hm_to_minutes(12, 30)),
    (hm_to_minutes(13, 0), hm_to_minutes(13, 30)),
    (hm_to_minutes(14, 30), hm_to_minutes(17, 0)),
    
    # Christian's busy intervals
    (hm_to_minutes(9, 0), hm_to_minutes(12, 30)),
    (hm_to_minutes(13, 0), hm_to_minutes(14, 0)),
    (hm_to_minutes(14, 30), hm_to_minutes(17, 0))
]

# First, sort the intervals by start time
busy_intervals.sort(key=lambda interval: interval[0])

# Merge overlapping busy intervals
merged_busy = []
for interval in busy_intervals:
    if not merged_busy:
        merged_busy.append(interval)
    else:
        last = merged_busy[-1]
        # If intervals overlap or touch, merge them.
        if interval[0] <= last[1]:
            merged_busy[-1] = (last[0], max(last[1], interval[1]))
        else:
            merged_busy.append(interval)

# Find free intervals within the working hours
free_intervals = []

# If there is free time before first busy interval
if work_start < merged_busy[0][0]:
    free_intervals.append((work_start, merged_busy[0][0]))

# Between merged busy intervals
for i in range(len(merged_busy) - 1):
    free_intervals.append((merged_busy[i][1], merged_busy[i+1][0]))

# If there is free time after the last busy interval
if merged_busy[-1][1] < work_end:
    free_intervals.append((merged_busy[-1][1], work_end))

# Look for the first free interval that fits the meeting_duration
meeting_slot = None
for start, end in free_intervals:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

# Format the result
if meeting_slot:
    meeting_time_str = f"{minutes_to_hm(meeting_slot[0])}:{minutes_to_hm(meeting_slot[1])}"
    day_of_week = "Monday"
    print(f"{day_of_week} {meeting_time_str}")
else:
    print("No available slot found during working hours.")