def time_to_minutes(t):
    """Converts a time string 'HH:MM' to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Converts minutes since midnight to a time string 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def intersect_intervals(intervals1, intervals2):
    """Finds the intersection of two lists of intervals.
       Each interval is a tuple (start, end) where times are in minutes."""
    result = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            result.append((start_overlap, end_overlap))
        # Move to next interval in the list that finishes earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Workday start and end (09:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Each participant's free intervals (in minutes) within the work hours.
# For those with busy intervals provided, we calculate their free intervals.
# If the participant is free all day, then free interval is the whole period.
# Busy intervals are half-open: start inclusive, end exclusive.

# Andrea: free all day.
andrea_free = [(work_start, work_end)]

# Jack busy: 09:00-09:30, 14:00-14:30.
# So free: 09:30-14:00 and 14:30-17:00.
jack_free = [
    (time_to_minutes("09:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), work_end)
]

# Madison busy: 09:30-10:30, 13:00-14:00, 15:00-15:30, 16:30-17:00.
# So free: 09:00-09:30, 10:30-13:00, 14:00-15:00, 15:30-16:30.
madison_free = [
    (work_start, time_to_minutes("09:30")),
    (time_to_minutes("10:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Rachel busy: 09:30-10:30, 11:00-11:30, 12:00-13:30, 14:30-15:30, 16:00-17:00.
# So free: 09:00-09:30, 10:30-11:00, 11:30-12:00, 13:30-14:30, 15:30-16:00.
rachel_free = [
    (work_start, time_to_minutes("09:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Douglas busy: 09:00-11:30, 12:00-16:30.
# So free: 11:30-12:00, 16:30-17:00.
douglas_free = [
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("16:30"), work_end)
]

# Ryan busy: 09:00-09:30, 13:00-14:00, 14:30-17:00.
# So free: 09:30-13:00, 14:00-14:30.
ryan_free = [
    (time_to_minutes("09:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30"))
]

# List of free intervals for all participants.
participants_free = [andrea_free, jack_free, madison_free, rachel_free, douglas_free, ryan_free]

# Compute the intersection of free intervals across all participants.
common_free = participants_free[0]
for free in participants_free[1:]:
    common_free = intersect_intervals(common_free, free)

# Looking for an interval that is at least 30 minutes long.
meeting_duration = 30
proposed_start = None

for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_start = start
        break

if proposed_start is not None:
    proposed_end = proposed_start + meeting_duration
    meeting_day = "Monday"
    print(f"{minutes_to_time(proposed_start)}:{minutes_to_time(proposed_end)} on {meeting_day}")
else:
    print("No available time slot found.")