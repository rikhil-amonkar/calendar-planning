def find_meeting_time(participants_schedules, duration, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_min = duration * 60

    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules.values():
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))

    # Sort intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))

    # Find available slots
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
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))

    return None

# Define participants' schedules
participants_schedules = {
    "Patrick": ["13:30 to 14:00", "14:30 to 15:00"],
    "Shirley": ["9:00 to 9:30", "11:00 to 11:30", "12:00 to 12:30", "14:30 to 15:00", "16:00 to 17:00"],
    "Jeffrey": ["9:00 to 9:30", "10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "16:00 to 17:00"],
    "Gloria": ["11:30 to 12:00", "15:00 to 15:30"],
    "Nathan": ["9:00 to 9:30", "10:30 to 12:00", "14:00 to 17:00"],
    "Angela": ["9:00 to 9:30", "10:00 to 11:00", "12:30 to 15:00", "15:30 to 16:30"],
    "David": ["9:00 to 9:30", "10:00 to 10:30", "11:00 to 14:00", "14:30 to 16:30"]
}

# Meeting parameters
meeting_duration = 30  # minutes
work_hours_start = "9:00"
work_hours_end = "17:00"
day_of_week = "Monday"

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}} {day_of_week}")
else:
    print("No suitable time found.")