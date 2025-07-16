def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration_minutes):
    # Convert all time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    meeting_duration = meeting_duration_minutes

    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules.values():
        for busy in schedule:
            start = time_to_minutes(busy[0])
            end = time_to_minutes(busy[1])
            busy_intervals.append((start, end))

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
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))

    # Find available slots by looking at gaps between busy intervals and work hours
    available_slots = []
    prev_end = work_start

    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Find the first available slot that can fit the meeting
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))

    return None

# Define the participants' schedules
participants_schedules = {
    'Andrea': [],
    'Jack': [('9:00', '9:30'), ('14:00', '14:30')],
    'Madison': [('9:30', '10:30'), ('13:00', '14:00'), ('15:00', '15:30'), ('16:30', '17:00')],
    'Rachel': [('9:30', '10:30'), ('11:00', '11:30'), ('12:00', '13:30'), ('14:30', '15:30'), ('16:00', '17:00')],
    'Douglas': [('9:00', '11:30'), ('12:00', '16:30')],
    'Ryan': [('9:00', '9:30'), ('13:00', '14:00'), ('14:30', '17:00')]
}

# Define work hours and meeting duration
work_hours_start = '9:00'
work_hours_end = '17:00'
meeting_duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration_minutes)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}}")
    print("Monday")
else:
    print("No available time slot found.")