def time_to_minutes(time_str):
    """Converts a time string HH:MM to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to a time string HH:MM."""
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, busy_intervals):
    """
    Given a working interval (work_start, work_end) and a list of busy intervals,
    returns a sorted list of free intervals.
    All times are in minutes.
    """
    free = []
    current = work_start
    # Assume busy_intervals are sorted by start time
    for b_start, b_end in busy_intervals:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """
    Given two lists of intervals (each interval is a tuple (start, end) in minutes),
    return their intersection as a new list.
    """
    i, j = 0, 0
    intersections = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find the overlap between the two intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersections.append((start_overlap, end_overlap))
        # Move the pointer with the earlier finishing interval
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Meeting duration in minutes
meeting_duration = 30

# Day: Monday, working hours 09:00 to 17:00 (in minutes)
work_start = time_to_minutes("09:00")  # 540
work_end = time_to_minutes("17:00")    # 1020

# Participant schedules (busy intervals as (start, end) in minutes)
# Juan: busy 09:00-10:30 and 15:30-16:00; also cannot meet after 16:00.
juan_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]
# For Juan, restrict available working hours to before 16:00.
juan_work_end = time_to_minutes("16:00")  # 960

# Marilyn: busy 11:00-11:30 and 12:30-13:00.
marilyn_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]

# Ronald: busy 09:00-10:30, 12:00-12:30, 13:00-13:30, 14:00-16:30.
ronald_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:30"))
]

# Calculate free intervals for each participant.
juan_free = get_free_intervals(work_start, juan_work_end, juan_busy)
marilyn_free = get_free_intervals(work_start, work_end, marilyn_busy)
ronald_free = get_free_intervals(work_start, work_end, ronald_busy)

# Compute the common free intervals among all three.
common_free = intersect_intervals(juan_free, marilyn_free)
common_free = intersect_intervals(common_free, ronald_free)

# Find the earliest time slot that can accommodate the meeting duration.
meeting_start = None
meeting_end = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

if meeting_start is not None:
    # Format the result as HH:MM:HH:MM and include the day of the week.
    result_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day_of_week = "Monday"
    print(f"{day_of_week} {result_time}")
else:
    print("No available slot found.")