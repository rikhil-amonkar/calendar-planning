from datetime import datetime, timedelta

# Utility functions to work with time in minutes and string formatting
def time_to_minutes(time_str):
    # time_str is "HH:MM"
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def subtract_busy_from_interval(free_interval, busy_intervals):
    """Given a free_interval (start, end) and a list of busy_intervals (tuples),
    subtracts the busy intervals from the free_interval and returns list of resulting free intervals.
    Assumes busy_intervals are sorted and non overlapping."""
    free_parts = []
    current_start, current_end = free_interval
    for b_start, b_end in busy_intervals:
        # if busy interval doesn't overlap at all, continue
        if b_end <= current_start or b_start >= current_end:
            continue
        # if there's free time before the busy interval, add it
        if b_start > current_start:
            free_parts.append((current_start, b_start))
        # update current_start to the end of busy interval
        current_start = max(current_start, b_end)
    if current_start < current_end:
        free_parts.append((current_start, current_end))
    return free_parts

def compute_free_intervals(busy_intervals, work_interval):
    """Calculates free intervals given busy intervals and a working interval.
    busy_intervals: list of (start, end) in minutes.
    work_interval: (start, end) in minutes."""
    busy_intervals_sorted = sorted(busy_intervals, key=lambda x: x[0])
    free = subtract_busy_from_interval(work_interval, busy_intervals_sorted)
    return free

def intersect_intervals(intervals1, intervals2):
    """Given two lists of intervals, compute their intersection."""
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        # Find overlapping part
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        # Move forward in the list that ends earlier
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def find_common_free_interval(participants_free, meeting_duration):
    # participants_free: list of free interval lists for each participant
    # reduce pairwise intersection of all free intervals
    common_free = participants_free[0]
    for free in participants_free[1:]:
        common_free = intersect_intervals(common_free, free)
        if not common_free:
            break
    # now, choose the earliest interval with enough duration for meeting_duration
    for start, end in common_free:
        if end - start >= meeting_duration:
            return start, start + meeting_duration
    return None

# Define working hours (9:00 to 17:00 in minutes since midnight)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
work_interval = (work_start, work_end)

meeting_duration = 30  # in minutes

# Busy schedules for each participant on Monday
# Each busy interval is (start, end) in minutes. Times are given in HH:MM.
schedules_busy = {
    "Tyler": [],  # free all day
    "Kelly": [],  # free all day
    "Stephanie": [
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    "Hannah": [],  # free all day
    "Joe": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("17:00"))
    ],
    "Diana": [
        (time_to_minutes("09:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    "Deborah": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# Compute free intervals for each participant
participants_free = []
for name, busy in schedules_busy.items():
    free_intervals = compute_free_intervals(busy, work_interval)
    participants_free.append(free_intervals)

# Find a common free interval of meeting_duration minutes
result = find_common_free_interval(participants_free, meeting_duration)

day_of_week = "Monday"
if result:
    start, end = result
    start_str = minutes_to_time_str(start)
    end_str = minutes_to_time_str(end)
    # Format as requested: HH:MM:HH:MM with the day of the week
    print(f"{day_of_week} {start_str}:{end_str}")
else:
    print("No common free interval found.")