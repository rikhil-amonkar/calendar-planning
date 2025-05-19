def time_to_minutes(t):
    """Converts time string "HH:MM" to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Converts minutes since midnight to time string "HH:MM"."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def invert_intervals(busy, start, end):
    """Given a list of busy intervals (in minutes) within [start, end],
    returns the list of free intervals in that window."""
    free = []
    current = start
    for bstart, bend in sorted(busy):
        if current < bstart:
            free.append((current, bstart))
        current = max(current, bend)
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Intersect two lists of intervals. Each interval is a tuple (start, end)."""
    result = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Intersection of intervals if they overlap:
        start_inter = max(start1, start2)
        end_inter = min(end1, end2)
        if start_inter < end_inter:
            result.append((start_inter, end_inter))
        # Move the pointer that ends first:
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Meeting parameters
meeting_duration = 30  # minutes
workday_start = time_to_minutes("09:00")
workday_end = time_to_minutes("17:00")
meeting_day = "Monday"

# Participants' busy intervals in minutes on Monday
# Jeffrey busy: 9:30-10:00, 10:30-11:00
jeffrey_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
]

# Virginia busy: 9:00-9:30, 10:00-10:30, 14:30-15:00, 16:00-16:30
virginia_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30")),
]

# Melissa busy: 9:00-11:30, 12:00-12:30, 13:00-15:00, 16:00-17:00
melissa_busy = [
    (time_to_minutes("09:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00")),
]
# Additionally, Melissa prefers not to meet after 14:00.
melissa_latest_end = time_to_minutes("14:00")

# Compute free intervals for each participant within workday hours
jeffrey_free = invert_intervals(jeffrey_busy, workday_start, workday_end)
virginia_free = invert_intervals(virginia_busy, workday_start, workday_end)
melissa_free = invert_intervals(melissa_busy, workday_start, workday_end)

# Intersect free intervals for Jeffrey and Virginia
common_free = intersect_intervals(jeffrey_free, virginia_free)
# Then intersect with Melissa's free intervals
common_free = intersect_intervals(common_free, melissa_free)

# Since Melissa prefers not to have a meeting after 14:00, we further restrict the intervals.
adjusted_common_free = []
for start, end in common_free:
    # Restrict the end time to not pass the latest acceptable end for Melissa.
    end = min(end, melissa_latest_end)
    if end - start >= meeting_duration:
        adjusted_common_free.append((start, end))

# Now search for an interval of meeting_duration in the adjusted common free intervals.
meeting_start = None
for start, end in adjusted_common_free:
    if end - start >= meeting_duration:
        meeting_start = start
        break

if meeting_start is not None:
    meeting_end = meeting_start + meeting_duration
    # Format the meeting time as "HH:MM:HH:MM" along with the day.
    result = f"{meeting_day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(result)
else:
    print("No available time slot found.")