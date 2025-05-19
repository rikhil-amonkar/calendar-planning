from datetime import datetime, timedelta

# Helper functions to convert time string to minutes and vice versa
def time_to_minutes(time_str):
    """Convert HH:MM time string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM time string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def subtract_busy_times(work_start, work_end, busy_times):
    """
    Given a working interval [work_start, work_end] and a list of busy intervals,
    return free intervals as a list of (start, end) in minutes.
    busy_times: list of tuples (busy_start, busy_end)
    """
    free_times = []
    current_start = work_start
    # Sort busy times
    busy_times.sort(key=lambda x: x[0])
    for busy_start, busy_end in busy_times:
        # If there's free time before this busy interval, record it.
        if busy_start > current_start:
            free_times.append((current_start, busy_start))
        # Move the current start forward
        current_start = max(current_start, busy_end)
    if current_start < work_end:
        free_times.append((current_start, work_end))
    return free_times

def intersection_intervals(intervals1, intervals2):
    """
    Compute the intersection intervals of two lists of intervals.
    Each interval is a tuple (start, end).
    Returns list of intersections that are non-empty.
    """
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap between the two intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersections.append((start_overlap, end_overlap))
        # Move the pointer that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Define working hours for Monday (9:00 to 17:00)
work_day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Define busy schedules for each participant
# James busy times
james_busy = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

# John busy times
john_busy = [
    (time_to_minutes("09:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]

# Calculate free times for each participant within working hours
james_free = subtract_busy_times(work_start, work_end, james_busy)
john_free = subtract_busy_times(work_start, work_end, john_busy)

# Find common free intervals between James and John
common_free = intersection_intervals(james_free, john_free)

# Search for a common free interval that can accommodate the meeting
meeting_time = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    start_time_str = minutes_to_time(meeting_time[0])
    end_time_str = minutes_to_time(meeting_time[1])
    print(f"{work_day} {start_time_str}:{end_time_str}")
else:
    print("No suitable meeting time found.")