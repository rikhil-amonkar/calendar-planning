def find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end):
    # Convert all time strings to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_min = duration * 60

    # Collect all busy intervals for each participant
    busy_intervals = []
    for participant, schedules in participans_schedules.items():
        for start, end in schedules:
            busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))

    # Add preferences as busy intervals
    for participant, pref in preferences.items():
        if pref.get('not_after'):
            not_after = time_to_minutes(pref['not_after'])
            busy_intervals.append((not_after, work_end))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_end = max(end, last_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append((start, end))

    # Find available slots by checking gaps between busy intervals
    available_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Find the first available slot that can fit the meeting duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            return minutes_to_time(meeting_start), minutes_to_time(meeting_end)

    return None, None

# Define the participants' schedules
participants_schedules = {
    'Anthony': [('09:30', '10:00'), ('12:00', '13:00'), ('16:00', '16:30')],
    'Pamela': [('09:30', '10:00'), ('16:30', '17:00')],
    'Zachary': [('09:00', '11:30'), ('12:00', '12:30'), ('13:00', '13:30'), ('14:30', '15:00'), ('16:00', '17:00')]
}

# Define preferences
preferences = {
    'Pamela': {'not_after': '14:30'}
}

# Define meeting parameters
meeting_duration = 1  # in hours
work_hours_start = '09:00'
work_hours_end = '17:00'
day = 'Monday'

# Find the meeting time
start_time, end_time = find_meeting_time(participants_schedules, preferences, meeting_duration, work_hours_start, work_hours_end)

# Output the result
if start_time and end_time:
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")