from datetime import datetime, timedelta

# Helper functions to convert time from string to minutes and vice versa.
def time_to_minutes(t):
    # t in "HH:MM"
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Compute free intervals given working hours and busy intervals.
def get_free_intervals(busy, work_start, work_end):
    # Busy intervals is a list of tuples (start, end) in minutes
    # Sort busy intervals by start time
    busy = sorted(busy, key=lambda x: x[0])
    free = []
    # Start from work_start
    current = work_start
    for b_start, b_end in busy:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

# Intersect two lists of intervals.
def intersect_intervals(intervals1, intervals2):
    result = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap between intervals1[i] and intervals2[j]
        overlap_start = max(start1, start2)
        overlap_end = min(end1, end2)
        if overlap_start < overlap_end:
            result.append((overlap_start, overlap_end))
        # Move to the next interval in the list that ends first.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Working hours: 09:00 to 17:00 in minutes.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Busy schedules for each participant on Monday (time intervals in minutes).
schedules = {
    "Joan": [("11:30", "12:00"), ("14:30", "15:00")],
    "Megan": [("09:00", "10:00"), ("14:00", "14:30"), ("16:00", "16:30")],
    "Austin": [],
    "Betty": [("09:30", "10:00"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:00", "16:30")],
    "Judith": [("09:00", "11:00"), ("12:00", "13:00"), ("14:00", "15:00")],
    "Terry": [("09:30", "10:00"), ("11:30", "12:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Kathryn": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "13:00"), ("14:00", "16:00"), ("16:30", "17:00")]
}

# Convert all busy times to minutes.
for person in schedules:
    schedules[person] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in schedules[person]]

# Compute free intervals for each participant.
free_intervals = {}
for person, busy in schedules.items():
    free_intervals[person] = get_free_intervals(busy, work_start, work_end)

# Compute common free intervals across all participants.
common_free = list(free_intervals.values())[0]
for person in list(free_intervals.keys())[1:]:
    common_free = intersect_intervals(common_free, free_intervals[person])

# Meeting duration: 30 minutes.
meeting_duration = 30

# Find the first interval which can accommodate the meeting.
meeting_time = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    meeting_start = minutes_to_time(meeting_time[0])
    meeting_end = minutes_to_time(meeting_time[1])
    print(f"Monday {meeting_start}:{meeting_end}")
else:
    print("No common free interval available.")