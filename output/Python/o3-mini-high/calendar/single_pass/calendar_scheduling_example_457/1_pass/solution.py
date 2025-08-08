def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM formatted string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    """Given a list of busy intervals (as (start, end) in minutes) sorted by start time,
    compute free intervals inside the work window [work_start, work_end]."""
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals."""
    i, j = 0, 0
    intersections = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find overlap
        inter_start = max(start1, start2)
        inter_end = min(end1, end2)
        if inter_start < inter_end:
            intersections.append((inter_start, inter_end))
        # Move the pointer with the earlier ending time
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Meeting parameters
meeting_duration = 30  # minutes
day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Busy intervals for each participant (times in HH:MM converted to minutes)
schedules = {
    "Andrea": [("09:30", "10:30"), ("13:30", "14:30")],
    "Ruth": [("12:30", "13:00"), ("15:00", "15:30")],
    "Steven": [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
               ("13:30", "14:00"), ("15:00", "16:00")],
    "Grace": [],  # No meetings the whole day
    "Kyle": [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "13:00"),
             ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Elijah": [("09:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:00"),
               ("15:30", "16:00"), ("16:30", "17:00")],
    "Lori": [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "13:30"),
             ("14:00", "16:00"), ("16:30", "17:00")]
}

# Convert busy intervals to minutes and sort them for each participant
for person, intervals in schedules.items():
    schedules[person] = sorted([(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals])

# Compute free intervals for each participant within the work hours
free_times = []
for person, busy in schedules.items():
    free = compute_free_intervals(busy, work_start, work_end)
    free_times.append(free)

# Find common free intervals across all participants by intersecting them one by one.
# Start with the free intervals of the first participant.
common_free = free_times[0]
for free in free_times[1:]:
    common_free = intersect_intervals(common_free, free)

# Look for a time slot that can accommodate the meeting duration
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    start_str = minutes_to_time(meeting_slot[0])
    end_str = minutes_to_time(meeting_slot[1])
    # The output format is HH:MM:HH:MM with the day of the week.
    print(f"{day} {{{start_str}:{end_str}}}")
else:
    print("No available slot found.")