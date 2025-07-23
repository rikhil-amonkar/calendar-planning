def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since start of the day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = int(minutes) // 60
        mm = int(minutes) % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)

    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []

    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(' to '))
            busy_intervals.append((start, end))

    # Sort all busy intervals
    busy_intervals.sort()

    # Merge overlapping or adjacent intervals
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

    # Find available slots by checking gaps between busy intervals and work hours
    available_slots = []
    prev_end = work_start

    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Check each available slot for sufficient duration
    meeting_duration_min = int(meeting_duration * 60)  # Convert to integer minutes
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= meeting_duration_min:
            return f"{minutes_to_time(slot_start)} to {minutes_to_time(slot_start + meeting_duration_min)}"

    return None

# Define participants' schedules
participants_schedules = [
    [],  # Walter has no meetings
    ["09:00 to 09:30", "10:00 to 10:30", "13:30 to 14:30", "15:00 to 16:00"],  # Cynthia
    ["10:00 to 11:00", "13:00 to 13:30", "14:00 to 15:00", "16:00 to 16:30"],  # Ann
    ["09:00 to 11:30", "12:30 to 13:30", "14:30 to 17:00"],  # Catherine
    ["09:00 to 09:30", "10:00 to 11:30", "12:00 to 12:30", "13:00 to 14:30", "15:00 to 16:00"],  # Kyle
]

meeting_duration = 0.5  # half an hour
work_hours_start = "09:00"
work_hours_end = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time.split(' to ')
    print(f"Monday {{{start_time} to {end_time}}}")
else:
    print("No suitable time found.")