from datetime import datetime, timedelta

def time_to_minutes(time_str):
    # Convert "HH:MM" to minutes from midnight
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Convert minutes to "HH:MM" string (zero padded)
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def invert_busy_intervals(busy_intervals, work_start, work_end):
    """
    Given busy intervals (each as a tuple of (start, end) minutes)
    and the working hours boundaries, return the free intervals.
    Assumes busy_intervals are non-overlapping and sorted.
    """
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, return the intersection as a list of intervals.
    Each interval is represented as a tuple (start, end) in minutes.
    """
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        # find overlapping section between the intervals
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:  # valid intersection
            intersection.append((start, end))
        # Move forward in the list whose interval ends first
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersection

def find_earliest_slot(intersected_intervals, duration):
    """
    Find the earliest interval from the intersected intervals that can fit the meeting duration.
    Duration is in minutes.
    """
    for start, end in intersected_intervals:
        if end - start >= duration:
            return (start, start + duration)
    return None

# Define working hours in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Define busy intervals in minutes for each participant
# Times are in "HH:MM" format and then converted to minutes.
# Denise: busy during 12:00-12:30 and 15:30-16:00
denise_busy = [
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Angela has no meetings
angela_busy = []

# Natalie: busy during 9:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
natalie_busy = [
    (time_to_minutes("09:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]

# Generate free intervals for each participant
denise_free = invert_busy_intervals(denise_busy, work_start, work_end)
angela_free = invert_busy_intervals(angela_busy, work_start, work_end)
natalie_free = invert_busy_intervals(natalie_busy, work_start, work_end)

# Find common free intervals by intersecting the free intervals of all participants
common_free = intersect_intervals(denise_free, angela_free)
common_free = intersect_intervals(common_free, natalie_free)

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Find the earliest available meeting slot that fits the required duration
slot = find_earliest_slot(common_free, meeting_duration)

if slot:
    meeting_start, meeting_end = slot
    # Format output in HH:MM:HH:MM format along with the day of the week (Monday)
    result_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day_of_week = "Monday"
    print(f"{day_of_week} {result_time}")
else:
    print("No available slot found.")