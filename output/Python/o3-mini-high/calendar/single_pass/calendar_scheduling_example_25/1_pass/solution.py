def minutes_to_str(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

def compute_free_intervals(working_interval, busy_intervals):
    free = []
    work_start, work_end = working_interval
    current = work_start
    # Assume busy_intervals are sorted by start time.
    for busy in busy_intervals:
        busy_start, busy_end = busy
        # Skip busy blocks that end before current free time starts
        if busy_end <= current:
            continue
        # If there is free time before the busy interval starts, add it
        if busy_start > current:
            free.append((current, min(busy_start, work_end)))
        current = max(current, busy_end)
        if current >= work_end:
            break
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    result = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap
        overlap_start = max(start1, start2)
        overlap_end = min(end1, end2)
        if overlap_start < overlap_end:
            result.append((overlap_start, overlap_end))
        # Move to the next interval from whichever finishes first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Meeting duration in minutes and the day of the meeting.
meeting_duration = 60
day = "Monday"

# Define working hours in minutes from midnight.
# Standard working hours 9:00 to 17:00
work_start = 9 * 60      # 540 minutes
work_end = 17 * 60       # 1020 minutes

# Pamela doesn't want to meet after 14:30,
# so her available window is limited to 9:00 to 14:30.
pamela_end = 14 * 60 + 30  # 870 minutes

# Define working intervals for each participant.
working_intervals = {
    "Anthony": (work_start, work_end),
    "Pamela": (work_start, pamela_end),
    "Zachary": (work_start, work_end)
}

# Define each participant's busy intervals (start, end) in minutes.
busy_intervals = {
    "Anthony": [
        (9 * 60 + 30, 10 * 60),   # 09:30-10:00
        (12 * 60, 13 * 60),       # 12:00-13:00
        (16 * 60, 16 * 60 + 30)   # 16:00-16:30
    ],
    "Pamela": [
        (9 * 60 + 30, 10 * 60),   # 09:30-10:00
        (16 * 60 + 30, 17 * 60)   # 16:30-17:00
    ],
    "Zachary": [
        (9 * 60, 11 * 60 + 30),   # 09:00-11:30
        (12 * 60, 12 * 60 + 30),  # 12:00-12:30
        (13 * 60, 13 * 60 + 30),  # 13:00-13:30
        (14 * 60 + 30, 15 * 60),  # 14:30-15:00
        (16 * 60, 17 * 60)        # 16:00-17:00
    ]
}

# Compute free intervals for each participant
free_intervals = {}
for person in working_intervals:
    free_intervals[person] = compute_free_intervals(working_intervals[person], busy_intervals[person])

# Find common free intervals by intersecting free times of all participants.
common_free = free_intervals["Anthony"]
common_free = intersect_intervals(common_free, free_intervals["Pamela"])
common_free = intersect_intervals(common_free, free_intervals["Zachary"])

# Look for the earliest common free interval that fits the meeting duration.
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    start_str = minutes_to_str(meeting_slot[0])
    end_str = minutes_to_str(meeting_slot[1])
    # Output format: HH:MM:HH:MM with the day of the week.
    print(f"{day} {start_str}:{end_str}")
else:
    print("No available time slot found.")