def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define meeting parameters
meeting_duration = 30  # in minutes
day = "Monday"

# Define working hours in minutes since midnight
work_start = 9 * 60   # 09:00 in minutes
work_end = 17 * 60    # 17:00 in minutes

# Define blocked intervals for each participant (in minutes since midnight)
# Michael: 09:30-10:30, 15:00-15:30, 16:00-16:30
michael_blocks = [
    (9 * 60 + 30, 10 * 60 + 30),
    (15 * 60, 15 * 60 + 30),
    (16 * 60, 16 * 60 + 30)
]

# Eric’s calendar is wide open, so no blocks.
eric_blocks = []

# Arthur: 09:00-12:00, 13:00-15:00, 15:30-16:00, 16:30-17:00
arthur_blocks = [
    (9 * 60, 12 * 60),
    (13 * 60, 15 * 60),
    (15 * 60 + 30, 16 * 60),
    (16 * 60 + 30, 17 * 60)
]

def get_free_times(blocked, work_start, work_end):
    """Return free time intervals as list of (start, end) given blocked intervals."""
    free = []
    current = work_start
    # Ensure blocked intervals are sorted
    for start, end in sorted(blocked):
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Return intersection of two lists of intervals."""
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap between the two intervals
        overlap_start = max(start1, start2)
        overlap_end = min(end1, end2)
        if overlap_start < overlap_end:
            intersection.append((overlap_start, overlap_end))
        # Advance the pointer with the smaller end time
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Calculate free intervals for each participant
michael_free = get_free_times(michael_blocks, work_start, work_end)
eric_free = [(work_start, work_end)]  # Eric is free the entire day
arthur_free = get_free_times(arthur_blocks, work_start, work_end)

# Calculate the common free intervals
common_free = intersect_intervals(michael_free, eric_free)
common_free = intersect_intervals(common_free, arthur_free)

# Find a slot that can fit the meeting duration
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    start_time_str = minutes_to_str(meeting_slot[0])
    end_time_str = minutes_to_str(meeting_slot[1])
    # Output format: "Monday HH:MM:HH:MM"
    print(f"{day} {start_time_str}:{end_time_str}")
else:
    print("No available slot found")