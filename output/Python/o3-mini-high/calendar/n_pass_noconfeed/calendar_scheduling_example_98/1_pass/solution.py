def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_slots(working_start, working_end, busy_intervals):
    """
    Given a working interval and a sorted list of busy intervals,
    return a list of free intervals.
    Each interval is a tuple (start, end) in minutes.
    """
    free_slots = []
    current_start = working_start
    for busy_start, busy_end in busy_intervals:
        if busy_start > current_start:
            free_slots.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    if current_start < working_end:
        free_slots.append((current_start, working_end))
    return free_slots

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals (each tuple of (start, end)), return their intersection.
    """
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Calculate overlapping portion
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:  # valid overlap
            intersection.append((start_overlap, end_overlap))
        # Move to next interval in the list that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Meeting duration in minutes
MEETING_DURATION = 30

# Working hours in minutes (9:00 to 17:00 is 540 to 1020)
# However, note that Juan cannot meet after 16:00, so his working window is 9:00 to 16:00 (540 to 960)
WEEKDAY = "Monday"
juan_working = (time_to_minutes("09:00"), time_to_minutes("16:00"))
others_working = (time_to_minutes("09:00"), time_to_minutes("17:00"))

# Busy intervals for each participant on Monday (in minutes)
# Juan is busy from 9:00 to 10:30 and 15:30 to 16:00
juan_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Marilyn is busy from 11:00 to 11:30 and 12:30 to 13:00
marilyn_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]

# Ronald is busy from 9:00 to 10:30, 12:00 to 12:30, 13:00 to 13:30, and 14:00 to 16:30
ronald_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:30"))
]

# Calculate free intervals for each participant
juan_free = get_free_slots(juan_working[0], juan_working[1], juan_busy)
marilyn_free = get_free_slots(others_working[0], others_working[1], marilyn_busy)
ronald_free = get_free_slots(others_working[0], others_working[1], ronald_busy)

# Compute the common free intervals across all participants
common_free = intersect_intervals(juan_free, marilyn_free)
common_free = intersect_intervals(common_free, ronald_free)

# Find the earliest common free interval that can accommodate the meeting duration.
meeting_start = None
meeting_end = None
for start, end in common_free:
    if end - start >= MEETING_DURATION:
        meeting_start = start
        meeting_end = start + MEETING_DURATION
        break

if meeting_start is not None:
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)
    # Output format: Day HH:MM:HH:MM (e.g., Monday 10:30:11:00)
    print(f"{WEEKDAY} {start_time_str}:{end_time_str}")
else:
    print("No available meeting slot found.")