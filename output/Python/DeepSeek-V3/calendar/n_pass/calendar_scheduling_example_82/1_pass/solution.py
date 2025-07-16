def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert all time strings to minutes since midnight for easier calculation
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
    meeting_duration_min = meeting_duration * 60

    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(':'))
            busy_intervals.append((start, end))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent busy intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                new_end = max(last_end, current_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append(interval)

    # Find available slots by looking at gaps between busy intervals and work hours
    available_slots = []
    prev_end = work_start

    for interval in merged:
        current_start, current_end = interval
        if current_start > prev_end:
            available_slots.append((prev_end, current_start))
        prev_end = max(prev_end, current_end)

    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Find the first available slot that can fit the meeting
    for slot in available_slots:
        start, end = slot
        if end - start >= meeting_duration_min:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration_min
            return minutes_to_time(meeting_start), minutes_to_time(meeting_end)

    return None, None

# Define participants' schedules
michael_schedule = [
    "09:30:10:30",
    "15:00:15:30",
    "16:00:16:30"
]

eric_schedule = []  # Wide open

arthur_schedule = [
    "09:00:12:00",
    "13:00:15:00",
    "15:30:16:00",
    "16:30:17:00"
]

# Combine all schedules
participants_schedules = [michael_schedule, eric_schedule, arthur_schedule]

# Find meeting time
meeting_start, meeting_end = find_meeting_time(
    participants_schedules,
    meeting_duration=30,
    work_hours_start="09:00",
    work_hours_end="17:00"
)

# Output the result
if meeting_start and meeting_end:
    print(f"{{{meeting_start}:{meeting_end}}}")
    print("Monday")
else:
    print("No suitable time found.")