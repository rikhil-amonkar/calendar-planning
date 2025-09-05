def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours and meeting duration (in minutes)
WORK_START = 9 * 60    # 9:00 AM in minutes
WORK_END = 17 * 60     # 17:00 (5:00 PM) in minutes
MEETING_DURATION = 30

# Busy intervals for each participant (times in minutes from midnight)
# For example, 10:30 AM is 10*60+30 = 630.
busy_schedule = {
    "Shirley": {
        "Monday": [
            (10 * 60 + 30, 11 * 60),     # 10:30 - 11:00
            (12 * 60, 12 * 60 + 30),      # 12:00 - 12:30
            (16 * 60, 16 * 60 + 30)       # 16:00 - 16:30
        ],
        "Tuesday": [
            (9 * 60 + 30, 10 * 60)        # 9:30 - 10:00
        ]
    },
    "Albert": {
        "Monday": [
            (9 * 60, 17 * 60)             # 9:00 - 17:00 (busy the whole day)
        ],
        "Tuesday": [
            (9 * 60 + 30, 11 * 60),        # 9:30 - 11:00
            (11 * 60 + 30, 12 * 60 + 30),   # 11:30 - 12:30
            (13 * 60, 16 * 60),            # 13:00 - 16:00
            (16 * 60 + 30, 17 * 60)        # 16:30 - 17:00
        ]
    }
}

# Preference: Shirley would rather not meet on Tuesday after 10:30,
# so on Tuesday the meeting must finish by or at 10:30 (i.e. end time <= 10:30).
PREFERRED_TUESDAY_END = 10 * 60 + 30  # 10:30 in minutes

def is_slot_free(day, start, end):
    """
    Check if the time slot from 'start' to 'end' is free for all participants on the given day.
    A slot is free if it does not overlap with any busy interval.
    """
    for person, schedule in busy_schedule.items():
        for busy_start, busy_end in schedule.get(day, []):
            # Overlap exists if the meeting starts before a busy interval ends
            # and the meeting ends after the busy interval starts.
            if start < busy_end and end > busy_start:
                return False
    return True

# List of days to try in order
for day in ["Monday", "Tuesday"]:
    # Determine the latest possible start time based on work hours
    # For Tuesday, also enforce that the meeting ends by 10:30.
    if day == "Tuesday":
        latest_start = PREFERRED_TUESDAY_END - MEETING_DURATION
    else:
        latest_start = WORK_END - MEETING_DURATION

    meeting_found = False
    # Try every possible starting minute between WORK_START and latest_start (inclusive)
    for start in range(WORK_START, latest_start + 1):
        end = start + MEETING_DURATION
        # Extra check for Tuesday preference (meeting must finish by 10:30)
        if day == "Tuesday" and end > PREFERRED_TUESDAY_END:
            continue
        if is_slot_free(day, start, end):
            start_str = to_time_str(start)
            end_str = to_time_str(end)
            # Output in the required format: day and {HH:MM:HH:MM}
            print(f"{day} {{{start_str}:{end_str}}}")
            meeting_found = True
            break
    if meeting_found:
        break