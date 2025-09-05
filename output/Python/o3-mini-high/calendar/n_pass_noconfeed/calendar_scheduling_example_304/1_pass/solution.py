def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def invert_intervals(busy, start, end):
    """Given a list of busy intervals (in minutes) sorted by start time,
       return a list of free intervals between [start, end]."""
    free = []
    current = start
    for bstart, bend in busy:
        # If the busy interval ends before our current free slot starts, skip it.
        if bend <= current:
            continue
        # If the busy interval starts after the current free slot,
        # then the portion between current and bstart is free.
        if bstart > current:
            free.append((current, min(bstart, end)))
        current = max(current, bend)
        if current >= end:
            break
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Return the intersection of two lists of intervals."""
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlapping part:
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            result.append((start_overlap, end_overlap))
        # Move the pointer that ends earlier.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Define effective working period (due to Janice's preference, meeting must be before 13:00)
# Work hours are 09:00 to 17:00 but Janice prefers not after 13:00, so we use 09:00 to 13:00.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("13:00")  # Meeting must be entirely before 13:00

# Meeting duration in minutes
meeting_duration = 30

# Participant busy schedules (as given, in HH:MM format)
schedules = {
    "Christine": [("09:30", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Janice":    [],  # free entire day
    "Bobby":     [("12:00", "12:30"), ("14:30", "15:00")],
    "Elizabeth": [("09:00", "09:30"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Tyler":     [("09:00", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Edward":    [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")]
}

# Convert busy intervals into minutes and sort them
participant_free = {}
for person, intervals in schedules.items():
    busy_intervals = []
    for start_str, end_str in intervals:
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        # Only consider busy intervals that overlap the effective working window.
        if end_min <= work_start or start_min >= work_end:
            continue
        # Clip the busy interval to the effective window
        busy_intervals.append((max(start_min, work_start), min(end_min, work_end)))
    busy_intervals.sort()
    free_intervals = invert_intervals(busy_intervals, work_start, work_end)
    participant_free[person] = free_intervals

# Now, find the common free intervals among all participants.
# Start with the full effective window as the initial common free interval.
common_free = [(work_start, work_end)]
for free in participant_free.values():
    common_free = intersect_intervals(common_free, free)

# Look for an interval that can accommodate the meeting duration.
meeting_time = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    meeting_start, meeting_end = meeting_time
    # Format output as HH:MM:HH:MM and day of the week
    output_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day = "Monday"
    print(f"{output_time} {day}")
else:
    print("No available meeting slot found.")