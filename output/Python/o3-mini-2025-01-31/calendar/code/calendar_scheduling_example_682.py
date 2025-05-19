def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def subtract_busy(time_interval, busy_intervals):
    """
    Given a free time_interval [start, end] (in minutes) and a list of busy_intervals,
    subtract the busy times and return a list of free intervals.
    """
    free = []
    current_start = time_interval[0]
    for b_start, b_end in sorted(busy_intervals):
        if b_start > current_start:
            free.append((current_start, min(b_start, time_interval[1])))
        current_start = max(current_start, b_end)
        if current_start >= time_interval[1]:
            break
    if current_start < time_interval[1]:
        free.append((current_start, time_interval[1]))
    return free

def intersect_intervals(intervals1, intervals2):
    """Find intersections between two lists of intervals."""
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Meeting parameters
meeting_duration = 30  # minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
work_period = (work_start, work_end)

# Schedule for Tuesday for Amanda and Nathan based on the given constraints:
# Amanda's busy intervals (Tuesday)
amanda_busy_times = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Nathan's busy intervals (Tuesday)
nathan_busy_times = [
    (time_to_minutes("09:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Constraint: Amanda does not want to meet on Tuesday after 11:00.
# So for Tuesday, Amanda's effective meeting window becomes from available free times that start before 11:00.
# Compute free intervals for both on Tuesday
amanda_free = subtract_busy(work_period, amanda_busy_times)
nathan_free = subtract_busy(work_period, nathan_busy_times)

# Intersect the free times
common_free = intersect_intervals(amanda_free, nathan_free)

# Filter the intersections that allow a meeting of at least meeting_duration minutes 
# and also satisfy Amanda's Tuesday constraint (meeting must end by 11:00, i.e., must start early enough)
valid_slots = []
for start, end in common_free:
    if end - start >= meeting_duration:
        # For Amanda, if meeting is on Tuesday, meeting start must be such that the meeting ends by 11:00
        # So, meeting start must be no later than 10:30.
        latest_start = min(end - meeting_duration, time_to_minutes("10:30"))
        if start <= latest_start:
            # Choose the earliest possible start time that satisfies both conditions
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            # Make sure meeting_end does not exceed 11:00
            if meeting_end <= time_to_minutes("11:00"):
                valid_slots.append((meeting_start, meeting_end))
                break

if valid_slots:
    slot_start, slot_end = valid_slots[0]
    day = "Tuesday"
    output = f"{minutes_to_time(slot_start)}:{minutes_to_time(slot_end)} on {day}"
    print(output)
else:
    print("No valid meeting slot found.")