def find_meeting_time(participants_schedules, preferences, duration_hours, work_hours_start, work_hours_end, day):
    # Convert time inputs to minutes since 9:00 (work_hours_start)
    def time_to_minutes(time_input):
        if isinstance(time_input, int):
            return (time_input - 9) * 60  # Assuming work_hours_start is 9
        hh, mm = map(int, time_input.split(':'))
        return (hh - 9) * 60 + mm  # Using 9 as base since work_hours_start is 9

    def minutes_to_time(minutes):
        hh = 9 + minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Convert work hours to minutes (using 9 as base)
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = duration_hours * 60

    # Collect all busy intervals for all participants
    busy_intervals = []
    for participant, schedules in participants_schedules.items():
        for start, end in schedules:
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_intervals.append((start_min, end_min))

    # Add preference constraints as busy intervals
    for participant, pref in preferences.items():
        if pref.get('not_after'):
            not_after_min = time_to_minutes(pref['not_after'])
            busy_intervals.append((not_after_min, work_end))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1][1] = max(last_end, end)
            else:
                merged.append([start, end])

    # Find available slots between busy intervals
    available_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Check each available slot for duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (
                day,
                f"{minutes_to_time(meeting_start)}-{minutes_to_time(meeting_end)}"
            )

    return None

# Define the problem
participants_schedules = {
    'Ryan': [('9:00', '9:30'), ('12:30', '13:00')],
    'Ruth': [],
    'Denise': [('9:30', '10:30'), ('12:00', '13:00'), ('14:30', '16:30')],
}

preferences = {
    'Denise': {'not_after': '12:30'},
}

duration_hours = 1
work_hours_start = 9  # Now accepts either 9 or "9:00"
work_hours_end = 17   # Now accepts either 17 or "17:00"
day = 'Monday'

# Find the meeting time
result = find_meeting_time(
    participants_schedules,
    preferences,
    duration_hours,
    work_hours_start,
    work_hours_end,
    day
)

if result:
    day, time_range = result
    print(f"{day}: {time_range}")
else:
    print("No suitable time found.")