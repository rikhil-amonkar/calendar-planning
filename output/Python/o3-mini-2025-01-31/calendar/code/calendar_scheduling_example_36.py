def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting parameters
meeting_duration = 60  # in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
latest_denise_meeting_end = time_to_minutes("12:30")  # Denise doesn't want meetings after 12:30

# Busy schedules (intervals in minutes) for each participant on Monday
busy = {
    "Ryan": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
    ],
    "Ruth": [],  # No busy times for Ruth
    "Denise": [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:30")),
    ]
}

def is_slot_free(start, end):
    # Check if meeting slot [start, end) does not conflict with any busy intervals
    for person in busy:
        for b_start, b_end in busy[person]:
            # If meeting starts before busy ends and ends after busy starts, they overlap.
            if start < b_end and end > b_start:
                return False
    return True

# We'll iterate over possible start times within working hours to find the first available one.
available_slot = None
for start in range(work_start, work_end - meeting_duration + 1):
    end = start + meeting_duration
    # Enforce Denise's constraint: meeting must end no later than 12:30.
    if end > latest_denise_meeting_end:
        continue
    if is_slot_free(start, end):
        available_slot = (start, end)
        break

if available_slot:
    start_time_str = minutes_to_time(available_slot[0])
    end_time_str = minutes_to_time(available_slot[1])
    # Output in the format: HH:MM:HH:MM along with the day of the week.
    print(f"Monday {start_time_str}:{end_time_str}")
else:
    print("No available time slot found.")