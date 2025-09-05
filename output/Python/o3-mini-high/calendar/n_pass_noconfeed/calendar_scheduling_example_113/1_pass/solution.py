def to_minutes(time_str):
    hh, mm = map(int, time_str.split(":"))
    return hh * 60 + mm

def minutes_to_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Workday parameters
work_start = to_minutes("09:00")   # 540 minutes
work_end = to_minutes("17:00")     # 1020 minutes
meeting_duration = 30  # in minutes

# Busy intervals for each participant on Monday, in minutes
bradley_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("12:30"), to_minutes("13:00")),
    (to_minutes("13:30"), to_minutes("14:00")),
    (to_minutes("15:30"), to_minutes("16:00"))
]

teresa_busy = [
    (to_minutes("10:30"), to_minutes("11:00")),
    (to_minutes("12:00"), to_minutes("12:30")),
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("14:30"), to_minutes("15:00"))
]

elizabeth_busy = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("10:30"), to_minutes("11:30")),
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("15:30"), to_minutes("17:00"))
]

christian_busy = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("10:30"), to_minutes("17:00"))
]

# Combine all busy schedules into one list for easy checking
all_busy = [bradley_busy, teresa_busy, elizabeth_busy, christian_busy]

def is_slot_free(start, busy_intervals):
    """
    Checks if a meeting slot [start, start + meeting_duration) conflicts
    with any interval in busy_intervals.
    """
    end = start + meeting_duration
    for busy_start, busy_end in busy_intervals:
        # Overlap occurs if the meeting starts before the busy interval ends
        # and ends after the busy interval starts.
        if start < busy_end and end > busy_start:
            return False
    return True

def is_common_slot(start):
    """
    Returns True if all participants are free for the meeting slot starting at 'start'.
    """
    for busy in all_busy:
        if not is_slot_free(start, busy):
            return False
    return True

meeting_slot = None
# Iterate over all possible start times within working hours
for t in range(work_start, work_end - meeting_duration + 1):
    if is_common_slot(t):
        meeting_slot = (t, t + meeting_duration)
        break

if meeting_slot:
    start_time = minutes_to_time(meeting_slot[0])
    end_time = minutes_to_time(meeting_slot[1])
    # Output format: Day and time range as HH:MM:HH:MM (e.g., "Monday 10:00:10:30")
    print(f"Monday {start_time}:{end_time}")
else:
    print("No available time slot found.")