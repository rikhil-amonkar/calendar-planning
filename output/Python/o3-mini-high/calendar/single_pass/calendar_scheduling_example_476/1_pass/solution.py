def to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define work hours and meeting duration (in minutes)
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30

# Roger’s preference: meeting not before 12:30
roger_earliest = to_minutes("12:30")

# Busy intervals for each participant on Monday (times in minutes)
busy = {
    "Daniel": [],
    "Kathleen": [
        (to_minutes("14:30"), to_minutes("15:30"))
    ],
    "Carolyn": [
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("13:30"))
    ],
    "Roger": [],
    "Cheryl": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("11:30")),
        (to_minutes("12:30"), to_minutes("13:30")),
        (to_minutes("14:00"), to_minutes("17:00"))
    ],
    "Virginia": [
        (to_minutes("09:30"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("17:00"))
    ],
    "Angela": [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:00"), to_minutes("16:30"))
    ]
}

def is_slot_free(candidate_start):
    candidate_end = candidate_start + meeting_duration
    # Ensure meeting is within work hours
    if candidate_start < work_start or candidate_end > work_end:
        return False
    # Check against each participant's busy intervals
    for person, intervals in busy.items():
        for interval_start, interval_end in intervals:
            # If candidate meeting overlaps a busy interval, it's not free.
            if candidate_start < interval_end and candidate_end > interval_start:
                return False
    return True

# Iterate over possible start times (in minutes) starting at Roger's earliest preference
meeting_start = None
for candidate in range(roger_earliest, work_end - meeting_duration + 1):
    if is_slot_free(candidate):
        meeting_start = candidate
        break

if meeting_start is not None:
    meeting_end = meeting_start + meeting_duration
    meeting_time_str = f"{to_hhmm(meeting_start)}:{to_hhmm(meeting_end)}"
    meeting_day = "Monday"
    print(meeting_day)
    print(meeting_time_str)
else:
    print("No available time slot found.")