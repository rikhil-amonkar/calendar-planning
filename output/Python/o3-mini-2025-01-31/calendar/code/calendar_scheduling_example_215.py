from datetime import timedelta

# Define work day start and end (in minutes from midnight)
WORK_START = 9 * 60      # 9:00 in minutes (540)
WORK_END = 17 * 60       # 17:00 in minutes (1020)
MEETING_DURATION = 30    # Duration in minutes

# Participant busy schedules represented as (start_minute, end_minute) intervals.
# Times are measured in minutes from midnight.
busy_times = {
    "Steven": [],  # free the entire day
    "Roy": [],     # free the entire day
    "Cynthia": [
        (9 * 60 + 30, 10 * 60 + 30),  # 09:30 to 10:30
        (11 * 60 + 30, 12 * 60),       # 11:30 to 12:00
        (13 * 60, 13 * 60 + 30),       # 13:00 to 13:30
        (15 * 60, 16 * 60)             # 15:00 to 16:00
    ],
    "Lauren": [
        (9 * 60, 9 * 60 + 30),         # 09:00 to 09:30
        (10 * 60 + 30, 11 * 60),        # 10:30 to 11:00
        (11 * 60 + 30, 12 * 60),        # 11:30 to 12:00
        (13 * 60, 13 * 60 + 30),        # 13:00 to 13:30
        (14 * 60, 14 * 60 + 30),        # 14:00 to 14:30
        (15 * 60, 15 * 60 + 30),        # 15:00 to 15:30
        (16 * 60, 17 * 60)             # 16:00 to 17:00
    ],
    "Robert": [
        (10 * 60 + 30, 11 * 60),       # 10:30 to 11:00
        (11 * 60 + 30, 12 * 60),       # 11:30 to 12:00
        (12 * 60 + 30, 13 * 60 + 30),   # 12:30 to 13:30
        (14 * 60, 16 * 60)             # 14:00 to 16:00
    ]
}

def is_interval_free(interval, busy_intervals):
    """Check if a given meeting interval (start, end) does not overlap any busy intervals."""
    start, end = interval
    for busy_start, busy_end in busy_intervals:
        # Check for any overlap
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

def format_time(minutes):
    """Return string formatted as HH:MM for a given minutes from midnight."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Try every possible start time within work hours (minute by minute)
proposed_interval = None
for start in range(WORK_START, WORK_END - MEETING_DURATION + 1):
    end = start + MEETING_DURATION
    interval = (start, end)
    # Check if all participants are free during this interval
    if all(is_interval_free(interval, busy_times.get(person, [])) for person in busy_times):
        proposed_interval = interval
        break

if proposed_interval:
    start_str = format_time(proposed_interval[0])
    end_str = format_time(proposed_interval[1])
    print(f"Monday {start_str}:{end_str}")
else:
    print("No available time found.")