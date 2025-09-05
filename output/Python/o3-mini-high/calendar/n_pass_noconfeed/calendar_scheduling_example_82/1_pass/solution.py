def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free_intervals(busy_times, work_start, work_end):
    """Calculate free intervals within working hours given busy intervals."""
    free_intervals = []
    current = work_start
    # Sort busy intervals if not already sorted.
    for start, end in sorted(busy_times):
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """Return intersection of two lists of intervals."""
    common = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            common.append((start, end))
        # Advance the pointer for whichever interval ends first.
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return common

# Meeting parameters
meeting_duration = 30  # in minutes
day_of_meeting = "Monday"
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Participants' busy schedules (times in HH:MM format)
michael_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

eric_busy = []  # Eric's calendar is completely free

arthur_busy = [
    (time_to_minutes("09:00"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Compute free intervals for each participant
michael_free = compute_free_intervals(michael_busy, work_start, work_end)
eric_free    = compute_free_intervals(eric_busy, work_start, work_end)
arthur_free  = compute_free_intervals(arthur_busy, work_start, work_end)

# Find common free intervals between all participants
common_free = intersect_intervals(michael_free, eric_free)
common_free = intersect_intervals(common_free, arthur_free)

# Choose the first available slot that can accommodate the meeting
meeting_start = None
meeting_end = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

if meeting_start is not None:
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output in the format HH:MM:HH:MM and the day of the week.
    print(f"{start_str}:{end_str} {day_of_meeting}")
else:
    print("No available slot found.")