def find_meeting_time(participants_schedule, duration, work_hours_start, work_hours_end, day):
    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_min = duration * 60

    # Collect all busy intervals for all participants
    busy_intervals = []
    for participant, schedule in participants_schedule.items():  # Fixed variable name here
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent intervals
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
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            return (
                f"{minutes_to_time(meeting_start)} to {minutes_to_time(meeting_end)}",
                day
            )

    return None

# Define the problem parameters
participants_schedule = {
    "Andrew": [],
    "Grace": [],
    "Samuel": [
        "09:00 to 10:30",
        "11:30 to 12:00",
        "13:00 to 13:30",
        "14:00 to 16:00",
        "16:30 to 17:00"
    ]
}
meeting_duration = 0.5  # in hours
work_hours_start = "09:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
meeting_time, day = find_meeting_time(participants_schedule, meeting_duration, work_hours_start, work_hours_end, day)

# Output the result
print(f"{{{meeting_time}}}")
print(day)