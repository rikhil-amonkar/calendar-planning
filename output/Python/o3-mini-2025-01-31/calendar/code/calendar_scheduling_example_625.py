from datetime import timedelta, datetime

def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    return datetime(2020, 1, 1, m // 60, m % 60).strftime("%H:%M")

# Meeting duration in minutes
meeting_duration = 30

# Work hours in minutes from 9:00 to 17:00
work_start = 9 * 60
work_end = 17 * 60

# Harold's busy slots in minutes
# Monday busy: 9:00-10:00 and 10:30-17:00
harold_busy_monday = [(9 * 60, 10 * 60), (10 * 60 + 30, work_end)]
# Tuesday busy: 9:00-9:30, 10:30-11:30, 12:30-13:30, 14:30-15:30, and 16:00-17:00
harold_busy_tuesday = [
    (9 * 60, 9 * 60 + 30),
    (10 * 60 + 30, 11 * 60 + 30),
    (12 * 60 + 30, 13 * 60 + 30),
    (14 * 60 + 30, 15 * 60 + 30),
    (16 * 60, work_end)
]

# Jeffrey is free the entire week so no busy intervals.
# We also incorporate Harold's preferences:
#    1. Avoid Monday (i.e., prefer Tuesday if possible)
#    2. For Tuesday, the meeting should be scheduled before 14:30

def find_free_slot(busy_slots, working_start, working_end, meeting_duration, latest_end=None):
    # Sort busy slots by start time
    busy_slots.sort()
    free_ranges = []
    # Start with time before first busy interval if available.
    current_start = working_start
    for start, end in busy_slots:
        if current_start < start:
            free_ranges.append((current_start, start))
        current_start = max(current_start, end)
    # Check after last busy interval.
    if current_start < working_end:
        free_ranges.append((current_start, working_end))
    
    # Filter free ranges by meeting duration
    for free_start, free_end in free_ranges:
        if free_end - free_start >= meeting_duration:
            # If a latest_end constraint is provided, ensure the meeting is before that time.
            # We require that the meeting end (start + meeting_duration) is <= latest_end.
            if latest_end is not None:
                # Find the earliest time in this free slot that fits the meeting and ends before latest_end.
                # The meeting can start at free_start at the earliest.
                meeting_start = free_start
                # if meeting_start + meeting_duration goes beyond latest_end, then skip this slot.
                if meeting_start + meeting_duration > latest_end:
                    # check if a later start in the interval could still yield an end time <= latest_end
                    # i.e. meeting_start must be <= latest_end - meeting_duration.
                    if free_end > latest_end - meeting_duration:
                        # we can set meeting_start = free_start if free_start is within allowed range
                        if free_start <= latest_end - meeting_duration:
                            meeting_start = free_start
                        else:
                            continue
                    else:
                        continue
                # Return meeting start and end times
                return meeting_start, meeting_start + meeting_duration
            else:
                return free_start, free_start + meeting_duration
    return None

# We prefer Tuesday given Harold's preference.
# Tuesday working time: 9:00 to 17:00, with additional constraint: meeting must finish before 14:30.
latest_end_tuesday = 14 * 60 + 30  # 14:30 in minutes

tuesday_slot = find_free_slot(
    harold_busy_tuesday,
    work_start,
    work_end,
    meeting_duration,
    latest_end=latest_end_tuesday
)

if tuesday_slot:
    meeting_day = "Tuesday"
    start_minutes, end_minutes = tuesday_slot
    meeting_time = f"{minutes_to_time(start_minutes)}:{minutes_to_time(end_minutes)}"
else:
    # fallback to Monday, if needed (though the problem assures a solution exists)
    monday_slot = find_free_slot(
        harold_busy_monday,
        work_start,
        work_end,
        meeting_duration
    )
    meeting_day = "Monday"
    start_minutes, end_minutes = monday_slot
    meeting_time = f"{minutes_to_time(start_minutes)}:{minutes_to_time(end_minutes)}"

print(f"{meeting_day} {meeting_time}")