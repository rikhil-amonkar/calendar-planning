def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, preferences):
    # Convert all time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = int(minutes // 60)  # Ensure hh is integer
        mm = int(minutes % 60)   # Ensure mm is integer
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_minutes = int(meeting_duration * 60)  # Ensure duration is integer

    # Collect all busy intervals for all participants
    busy_intervals = []
    for participant, schedules in participants_schedules.items():
        for interval in schedules:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))

    # Add preferences as busy intervals (e.g., Megan's preference to avoid before 10:00)
    for participant, pref in preferences.items():
        if pref.get('avoid_before'):
            avoid_time = time_to_minutes(pref['avoid_before'])
            busy_intervals.append((work_start, avoid_time))

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
                merged[-1][1] = max(end, last_end)
            else:
                merged.append([start, end])

    # Find available slots between work hours and busy intervals
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
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return minutes_to_time(meeting_start), minutes_to_time(meeting_end)

    return None, None

# Define the participants' schedules
participants_schedules = {
    'Kimberly': ['10:00 to 10:30', '11:00 to 12:00', '16:00 to 16:30'],
    'Megan': [],
    'Marie': ['10:00 to 11:00', '11:30 to 15:00', '16:00 to 16:30'],
    'Diana': ['09:30 to 10:00', '10:30 to 14:30', '15:30 to 17:00']
}

# Define preferences (e.g., Megan wants to avoid before 10:00)
preferences = {
    'Megan': {'avoid_before': '10:00'}
}

# Meeting details
meeting_duration = 0.5  # in hours
work_hours_start = '09:00'
work_hours_end = '17:00'
day_of_week = 'Monday'

# Find the meeting time
start_time, end_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, preferences)

if start_time and end_time:
    print(f"{{{start_time}:{end_time}}}")
    print(day_of_week)
else:
    print("No suitable time found.")