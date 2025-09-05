def time_to_minutes(time_str):
    """Convert HH:MM to minutes from midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes from midnight to HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, start_day, end_day):
    """Given a sorted list of busy intervals, return free intervals within work hours."""
    free_intervals = []
    current = start_day
    for interval in busy_intervals:
        if interval[0] > current:
            free_intervals.append((current, interval[0]))
        current = max(current, interval[1])
    if current < end_day:
        free_intervals.append((current, end_day))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """Intersect two lists of intervals and return the overlapping intervals."""
    intersection = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                intersection.append((start, end))
    return intersection

# Meeting parameters
meeting_duration = 60  # minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_day = "Monday"

# Busy intervals for each participant (converted to minutes)
stephanie_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

cheryl_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

bradley_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

steven_busy = [
    (time_to_minutes("09:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

# Compute free intervals for each participant within working hours
stephanie_free = get_free_intervals(stephanie_busy, work_start, work_end)
cheryl_free = get_free_intervals(cheryl_busy, work_start, work_end)
bradley_free = get_free_intervals(bradley_busy, work_start, work_end)
steven_free = get_free_intervals(steven_busy, work_start, work_end)

# Calculate common free intervals by intersecting all participants' free times
common_free = stephanie_free
for free in [cheryl_free, bradley_free, steven_free]:
    common_free = intersect_intervals(common_free, free)

# Find the earliest interval that can accommodate the meeting duration
proposed_meeting = None
for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_meeting = (start, start + meeting_duration)
        break

if proposed_meeting:
    start_time_str = minutes_to_time(proposed_meeting[0])
    end_time_str = minutes_to_time(proposed_meeting[1])
    # Format: Day HH:MM:HH:MM
    print(f"{meeting_day} {start_time_str}:{end_time_str}")
else:
    print("No available meeting time found.")