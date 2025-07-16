def find_meeting_time(participants_schedules, preferences, duration_hours, work_hours_start, work_hours_end, day):
    # Convert all time strings to minutes since 9:00 (work_hours_start)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - work_hours_start) * 60 + mm

    def minutes_to_time(minutes):
        hh = work_hours_start + minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

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
                f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
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
work_hours_start = 9
work_hours_end = 17
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
    start, end = time_range.split(':')
    print(f"{day}: {start}:{end}")
else:
    print("No suitable time found.")