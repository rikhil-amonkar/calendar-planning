from datetime import datetime, timedelta

def time_to_minutes(timestr):
    """Convert 'HH:MM' to minutes since midnight."""
    h, m = map(int, timestr.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    """Convert minutes since midnight to 'HH:MM' string."""
    return f"{minutes//60:02d}:{minutes%60:02d}"

# Define workday start and end in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Busy intervals for each participant as (start, end) times in minutes.
# All times are on Monday.
busy_schedules = {
    "Evelyn": [],  # free entire day
    "Joshua": [
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Kevin": [],  # free entire day
    "Gerald": [],  # free entire day
    "Jerry": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00"))
    ],
    "Jesse": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))
    ],
    "Kenneth": [
        (time_to_minutes("10:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

def is_time_available(start, end, busy_intervals):
    """Return True if the interval [start, end) does not conflict with any busy interval."""
    for bstart, bend in busy_intervals:
        # if meeting overlaps with a busy block, return False
        if start < bend and end > bstart:
            return False
    return True

def find_meeting_slot():
    # Loop through each possible minute in the workday where the meeting
    # can start and end within the work hours.
    for start in range(work_start, work_end - meeting_duration + 1):
        end = start + meeting_duration
        conflict = False
        # Check each participant's busy schedule
        for person, busy_intervals in busy_schedules.items():
            if not is_time_available(start, end, busy_intervals):
                conflict = True
                break
        if not conflict:
            return start, end
    return None, None

meeting_start, meeting_end = find_meeting_slot()

if meeting_start is not None:
    meeting_start_str = minutes_to_time(meeting_start)
    meeting_end_str = minutes_to_time(meeting_end)
    meeting_day = "Monday"
    # Output in the format {HH:MM:HH:MM} and day of the week
    print(meeting_day, f"{{{meeting_start_str}:{meeting_end_str}}}")
else:
    print("No available meeting slot found.")