def time_to_minutes(t):
    """Convert a time string 'HH:MM' to minutes past midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes past midnight to a time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, window_start, window_end):
    """Return a list of free time intervals within the window given busy intervals."""
    free = []
    # Start at the beginning of the window.
    current = window_start
    # Sort busy intervals by start time.
    busy_sorted = sorted(busy, key=lambda x: x[0])
    for start, end in busy_sorted:
        if start > current:
            free.append((current, min(start, window_end)))
        current = max(current, end)
        if current >= window_end:
            break
    if current < window_end:
        free.append((current, window_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Intersect two lists of intervals."""
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        # Find the overlap of the two intervals.
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            result.append((start, end))
        # Move to the next interval in the list that finishes first.
        if e1 < e2:
            i += 1
        else:
            j += 1
    return result

# Meeting parameters
meeting_duration = 60  # in minutes

# Define working hours and additional constraints.
# Work hours: 09:00 to 17:00 on Monday.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
# Denise prefers not to meet after 12:30, so the meeting must finish by 12:30.
denise_meeting_limit = time_to_minutes("12:30")

# For scheduling, the effective window is from work start until Denise's meeting limit.
effective_start = work_start
effective_end = denise_meeting_limit  # meeting must finish by 12:30

# Busy intervals for each participant (times in minutes).
# Ryan is busy from 09:00 to 09:30, and 12:30 to 13:00.
ryan_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]

# Ruth has no meetings.
ruth_busy = []

# Denise is busy from 09:30 to 10:30, 12:00 to 13:00, and 14:30 to 16:30.
denise_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:30"))
]

# Get free intervals within the effective window for each participant.
ryan_free = get_free_intervals(ryan_busy, effective_start, effective_end)
ruth_free = get_free_intervals(ruth_busy, effective_start, effective_end)
denise_free = get_free_intervals(denise_busy, effective_start, effective_end)

# Compute common free intervals by intersecting free times.
common_free = intersect_intervals(ryan_free, ruth_free)
common_free = intersect_intervals(common_free, denise_free)

# Find the earliest common free slot that can accommodate the meeting duration.
proposed_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_slot = (start, start + meeting_duration)
        break

# Output the result.
day_of_week = "Monday"
if proposed_slot:
    start_time_str = minutes_to_time(proposed_slot[0])
    end_time_str = minutes_to_time(proposed_slot[1])
    # Output in the format "HH:MM:HH:MM" along with the day of the week.
    print(f"{day_of_week} {start_time_str}:{end_time_str}")
else:
    print("No available meeting slot found.")