from datetime import datetime, timedelta

# Define time format helper functions
def str_to_minutes(time_str):
    """Convert HH:MM string to minutes from midnight."""
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_str(minutes):
    """Convert minutes from midnight to HH:MM string."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def find_free_slot(busy_periods, work_start, work_end, meeting_duration):
    """
    Given a sorted list of busy intervals (each as (start, end) in minutes),
    find the earliest free interval in [work_start, work_end] with at least meeting_duration minutes.
    """
    # Check free time before first meeting
    if busy_periods:
        if busy_periods[0][0] - work_start >= meeting_duration:
            return work_start, work_start + meeting_duration
    else:
        if work_end - work_start >= meeting_duration:
            return work_start, work_start + meeting_duration

    # Check free times between meetings
    for i in range(len(busy_periods) - 1):
        end_current = busy_periods[i][1]
        start_next = busy_periods[i+1][0]
        if start_next - end_current >= meeting_duration:
            return end_current, end_current + meeting_duration

    # Check free time after last meeting
    if work_end - busy_periods[-1][1] >= meeting_duration:
        return busy_periods[-1][1], busy_periods[-1][1] + meeting_duration

    return None

# Work hours (in minutes after midnight)
work_start = str_to_minutes("09:00")
work_end   = str_to_minutes("17:00")
meeting_duration = 30  # minutes

# James's busy schedules given as lists of (start, end) times on each day.
# Times are in HH:MM format and will be converted to minutes.
schedules = {
    "Monday": [
        ("09:00", "09:30"),
        ("10:30", "11:00"),
        ("12:30", "13:00"),
        ("14:30", "15:30"),
        ("16:30", "17:00")
    ],
    "Tuesday": [
        ("09:00", "11:00"),
        ("11:30", "12:00"),
        ("12:30", "15:30"),
        ("16:00", "17:00")
    ],
    "Wednesday": [
        ("10:00", "11:00"),
        ("12:00", "13:00"),
        ("13:30", "16:00")
    ],
    "Thursday": [
        ("09:30", "11:30"),
        ("12:00", "12:30"),
        ("13:00", "13:30"),
        ("14:00", "14:30"),
        ("16:30", "17:00")
    ]
}

# Cheryl's calendar is wide open, but she prefers not to meet on Wednesday.
# So we choose the following day priority order: Monday, Tuesday, Thursday, Wednesday.
day_priority = ["Monday", "Tuesday", "Thursday", "Wednesday"]

meeting_day = None
meeting_start = None
meeting_end = None

for day in day_priority:
    busy_periods = schedules.get(day, [])
    # Convert busy intervals to minutes and sort them
    busy_periods = sorted([(str_to_minutes(start), str_to_minutes(end)) for start, end in busy_periods])
    free_slot = find_free_slot(busy_periods, work_start, work_end, meeting_duration)
    if free_slot:
        meeting_day = day
        meeting_start, meeting_end = free_slot
        break

if meeting_day:
    # Format the meeting start and end times
    start_str = minutes_to_str(meeting_start)
    end_str = minutes_to_str(meeting_end)
    # Output in the format: HH:MM:HH:MM and day of the week
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No available meeting slot found.")