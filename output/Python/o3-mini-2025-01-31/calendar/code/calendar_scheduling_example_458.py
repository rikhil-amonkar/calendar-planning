from datetime import timedelta, datetime

# Helper functions to convert between time strings and minutes from midnight
def time_to_minutes(time_str):
    # time_str in "HH:MM"
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Each free interval is represented as (start, end) in minutes.
# Work day is 9:00 to 17:00.
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Meeting duration in minutes
meeting_duration = 30

# Since Wayne prefers to avoid meetings before 14:00, adjust his availability:
wayne_free = [(max(work_start, time_to_minutes("14:00")), work_end)]

# For Melissa, Catherine, Gregory, Victoria, Thomas, Jennifer, 
# We subtract busy times from the work hours.
# We'll construct the free intervals for each participant.

def invert_busy_intervals(busy_intervals, overall_start, overall_end):
    """
    Given a list of busy intervals as (start, end) in minutes,
    return free intervals in the overall range.
    Busy intervals assumed to be sorted and non-overlapping.
    """
    free = []
    current_start = overall_start
    for start, end in busy_intervals:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < overall_end:
        free.append((current_start, overall_end))
    return free

# Define busy intervals for participants (all times in 24-hour HH:MM format converted to minutes)
# For each participant the busy intervals on Monday are:

# Melissa: 10:00-11:00, 12:30-14:00, 15:00-15:30
melissa_busy = [
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Catherine: free all day.
catherine_free = [(work_start, work_end)]

# Gregory: 12:30-13:00, 15:30-16:00
gregory_busy = [
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Victoria: 9:00-9:30, 10:30-11:30, 13:00-14:00, 14:30-15:00, 15:30-16:30
victoria_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:30"))
]

# Thomas: 10:00-12:00, 12:30-13:00, 14:30-16:00
thomas_busy = [
    (time_to_minutes("10:00"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:00"))
]

# Jennifer: 9:00-9:30, 10:00-10:30, 11:00-13:00, 13:30-14:30, 15:00-15:30, 16:00-16:30
jennifer_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Compute free intervals for each participant who has busy intervals:
melissa_free = invert_busy_intervals(melissa_busy, work_start, work_end)
gregory_free = invert_busy_intervals(gregory_busy, work_start, work_end)
victoria_free = invert_busy_intervals(victoria_busy, work_start, work_end)
thomas_free = invert_busy_intervals(thomas_busy, work_start, work_end)
jennifer_free = invert_busy_intervals(jennifer_busy, work_start, work_end)

# For scheduling the meeting we need to consider everyone's constraints.
# We'll compute the intersection of all free intervals.
# Start by listing each participants' free intervals.
free_intervals = [
    wayne_free,
    melissa_free,
    catherine_free,
    gregory_free,
    victoria_free,
    thomas_free,
    jennifer_free
]

def intersect_intervals(int_list1, int_list2):
    """Intersect two lists of intervals"""
    result = []
    i, j = 0, 0
    while i < len(int_list1) and j < len(int_list2):
        start1, end1 = int_list1[i]
        start2, end2 = int_list2[j]
        # Find the intersection between these two intervals:
        intersect_start = max(start1, start2)
        intersect_end = min(end1, end2)
        if intersect_start < intersect_end:
            result.append((intersect_start, intersect_end))
        # Move forward in the list that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Compute the common intersection of free intervals for all participants:
common_free = free_intervals[0]
for intervals in free_intervals[1:]:
    common_free = intersect_intervals(common_free, intervals)

# Now, from the common free intervals, find an interval that can host the meeting.
meeting_time = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    meeting_start, meeting_end = meeting_time
    meeting_start_str = minutes_to_time(meeting_start)
    meeting_end_str = minutes_to_time(meeting_end)
    # Day of the week is Monday as per constraints.
    day = "Monday"
    print(f"{meeting_start_str}:{meeting_end_str} {day}")
else:
    print("No common free interval found.")