def time_to_minutes(t):
    """Convert a HH:MM string to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to a HH:MM string."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Define working hours and meeting duration.
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
MEETING_DURATION = 30

# Harold's busy times.
# Monday busy: 09:00-10:00 and 10:30-17:00.
busy_monday = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("17:00"))
]
# Tuesday busy: 09:00-09:30, 10:30-11:30, 12:30-13:30, 14:30-15:30, 16:00-17:00.
busy_tuesday = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

def compute_free_intervals(busy):
    """
    Given a list of busy intervals (start, end) in minutes,
    return a list of free intervals within working hours.
    """
    free = []
    current = WORK_START
    # Ensure busy intervals are sorted.
    for start, end in sorted(busy):
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < WORK_END:
        free.append((current, WORK_END))
    return free

# Calculate free intervals for Monday and Tuesday.
free_monday = compute_free_intervals(busy_monday)
free_tuesday = compute_free_intervals(busy_tuesday)

# Harold prefers to avoid Monday, so we try Tuesday first.
# Additionally, he prefers the meeting to be before 14:30 on Tuesday.
DEADLINE_TUESDAY = time_to_minutes("14:30")

def find_slot(free_intervals, meeting_duration, deadline=None):
    """
    Finds the earliest meeting slot within the free intervals.
    If a deadline is provided, the meeting must end no later than this time.
    Returns a tuple (start, end) in minutes or None if no slot exists.
    """
    for start, end in free_intervals:
        effective_end = end if deadline is None else min(end, deadline)
        if effective_end - start >= meeting_duration:
            return (start, start + meeting_duration)
    return None

# Try Tuesday first with the constraint that the meeting ends by 14:30.
meeting_slot = find_slot(free_tuesday, MEETING_DURATION, deadline=DEADLINE_TUESDAY)
meeting_day = "Tuesday"

# If no suitable slot is found on Tuesday, fall back to Monday.
if meeting_slot is None:
    meeting_slot = find_slot(free_monday, MEETING_DURATION)
    meeting_day = "Monday"

# Format the meeting time.
start_minutes, end_minutes = meeting_slot
meeting_time_str = f"{minutes_to_time(start_minutes)}:{minutes_to_time(end_minutes)}"

print(f"{meeting_day} {meeting_time_str}")