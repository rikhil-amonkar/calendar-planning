def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = meeting_duration * 60

    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []

    for schedule in participants_schedules:
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
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))

    # Find free slots by checking gaps between busy intervals and work hours
    free_slots = []
    prev_end = work_start

    for start, end in merged:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    if prev_end < work_end:
        free_slots.append((prev_end, work_end))

    # Find the first free slot that can accommodate the meeting
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))

    return None

# Define participants' schedules (each block is a start and end time)
participants_schedules = [
    [],  # Tyler is free
    [],  # Kelly is free
    [("11:00", "11:30"), ("14:30", "15:00")],  # Stephanie
    [],  # Hannah is free
    [("09:00", "09:30"), ("10:00", "12:00"), ("12:30", "13:00"), ("14:00", "17:00")],  # Joe
    [("09:00", "10:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],  # Diana
    [("09:00", "10:00"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "16:30")],  # Deborah
]

meeting_duration = 30  # minutes
work_hours_start = "09:00"
work_hours_end = "17:00"

result = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)
if result:
    start_time, end_time = result
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No suitable time found.")