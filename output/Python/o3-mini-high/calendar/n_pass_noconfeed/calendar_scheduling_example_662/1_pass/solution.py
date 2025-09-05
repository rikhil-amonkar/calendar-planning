def to_minutes(t):
    """Converts a time string "HH:MM" to minutes since midnight."""
    hh, mm = map(int, t.split(":"))
    return hh * 60 + mm

def to_timestr(m):
    """Converts minutes since midnight to a time string "HH:MM"."""
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

def get_free_intervals(work_start, work_end, blocked):
    """
    Given the work hours and a sorted list of blocked intervals (in minutes),
    returns a list of free intervals as (start, end) tuples.
    """
    free = []
    current = work_start
    for start, end in blocked:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """Compute the intersection of two lists of intervals."""
    common = []
    for s1, e1 in list1:
        for s2, e2 in list2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start > 0:
                common.append((start, end))
    return common

# Work day hours in minutes (9:00 to 17:00).
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
MEETING_DURATION = 60  # in minutes

# Define each participant's blocked intervals as strings for each day.
participants = {
    "Gary": {
        "Monday": [("09:30", "10:00"), ("11:00", "13:00"), ("14:00", "14:30"), ("16:30", "17:00")],
        "Tuesday": [("09:00", "09:30"), ("10:30", "11:00"), ("14:30", "16:00")]
    },
    "David": {
        "Monday": [("09:00", "09:30"), ("10:00", "13:00"), ("14:30", "16:30")],
        "Tuesday": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "12:30"), ("13:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")]
    }
}

# Convert all blocked times to minutes.
for person in participants:
    for day in participants[person]:
        intervals = participants[person][day]
        # Convert each (start, end) string tuple to a tuple of minutes.
        participants[person][day] = sorted([(to_minutes(s), to_minutes(e)) for s, e in intervals])

# Days to consider.
days = ["Monday", "Tuesday"]

meeting_scheduled = False

for day in days:
    free_intervals_by_person = {}
    
    # Compute free intervals for each person on the current day.
    for person in participants:
        blocked = participants[person].get(day, [])
        free_intervals_by_person[person] = get_free_intervals(WORK_START, WORK_END, blocked)
    
    # Find the common free intervals between Gary and David.
    common_free = intersect_intervals(free_intervals_by_person["Gary"], free_intervals_by_person["David"])
    
    # Look for an interval that can accommodate the meeting.
    for start, end in common_free:
        if end - start >= MEETING_DURATION:
            meeting_start = start
            meeting_end = start + MEETING_DURATION
            # Output the meeting time in the required format.
            print(f"{day} {to_timestr(meeting_start)}:{to_timestr(meeting_end)}")
            meeting_scheduled = True
            break
    if meeting_scheduled:
        break