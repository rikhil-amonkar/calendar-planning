def to_minutes(time_str):
    # Convert "HH:MM" to minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_time_str(minutes):
    # Convert minutes since midnight back to "HH:MM" format.
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def has_conflict(start, end, busy_intervals):
    # Check if the interval [start, end) overlaps with any busy interval.
    for b_start, b_end in busy_intervals:
        # Overlap exists if start is before busy end AND end is after busy start.
        if start < b_end and end > b_start:
            return True
    return False

# Meeting duration (in minutes)
meeting_duration = 30

# Workday boundaries in minutes (9:00 to 17:00)
work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")

# David's personal constraint: no meetings before 14:00 (i.e., 840 minutes)
david_earliest = to_minutes("14:00")

# Participant busy schedules (times are in minutes since midnight)
schedules = {
    "Natalie": [],  # free all day
    "David": [
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("14:30"), to_minutes("15:00"))
    ],
    "Douglas": [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("15:00"))
    ],
    "Ralph": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("12:30")),
        (to_minutes("13:30"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00"))
    ],
    "Jordan": [
        (to_minutes("09:00"), to_minutes("10:00")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("17:00"))
    ]
}

# We'll search for the earliest meeting slot that starts no earlier than 14:00.
candidate = max(work_start, david_earliest)
meeting_slot = None

while candidate + meeting_duration <= work_end:
    candidate_end = candidate + meeting_duration
    conflict_found = False
    for person, busy_times in schedules.items():
        if has_conflict(candidate, candidate_end, busy_times):
            conflict_found = True
            break
    if not conflict_found:
        meeting_slot = (candidate, candidate_end)
        break
    candidate += 1  # Try the next minute

if meeting_slot:
    start, end = meeting_slot
    start_str = to_time_str(start)
    end_str = to_time_str(end)
    # Output in the desired format with day of week and time range in HH:MM:HH:MM format.
    print("Monday", f"{start_str}:{end_str}")
else:
    print("No available slot found on Monday.")