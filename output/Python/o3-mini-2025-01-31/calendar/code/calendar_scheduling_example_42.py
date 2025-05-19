def time_to_minutes(t):
    """Converts HH:MM string to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    """Converts minutes since midnight to HH:MM format."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define working hours
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60

# Define busy intervals for each participant (start, end) as minutes since midnight
# Julie's busy intervals on Monday
julie_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Sean's busy intervals on Monday
sean_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

# Lori's busy intervals on Monday
lori_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("13:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Combine all busy intervals as a dictionary for clarity (though we check each separately)
schedules = {
    "Julie": julie_busy,
    "Sean": sean_busy,
    "Lori": lori_busy,
}

def is_free(start, duration, busy_intervals):
    """Check if a person is free for the whole duration starting from 'start'.
       busy_intervals is a list of (busy_start, busy_end) in minutes.
    """
    end = start + duration
    for busy_start, busy_end in busy_intervals:
        # if the meeting overlaps with a busy interval, return False
        if start < busy_end and end > busy_start:
            return False
    return True

def find_meeting_slot():
    # Check every minute candidate starting time from work_start to (work_end - meeting_duration)
    for candidate in range(work_start, work_end - meeting_duration + 1):
        if (is_free(candidate, meeting_duration, schedules["Julie"]) and
            is_free(candidate, meeting_duration, schedules["Sean"]) and
            is_free(candidate, meeting_duration, schedules["Lori"])):
            return candidate, candidate + meeting_duration
    return None

slot = find_meeting_slot()

if slot:
    start_time = minutes_to_time(slot[0])
    end_time = minutes_to_time(slot[1])
    day = "Monday"
    print(f"{day}, {start_time}:{end_time}")
else:
    print("No available slot satisfies the meeting constraints.")