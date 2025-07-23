def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day):
    # Convert all time strings to minutes since start of day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = duration_minutes

    # Collect all busy intervals for all participants
    all_busy = []
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(' to '))
            all_busy.append((start, end))

    # Sort all busy intervals by start time
    all_busy.sort()

    # Find free slots by merging all busy intervals
    merged = []
    for start, end in all_busy:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))

    # Generate free slots by checking gaps between merged busy intervals and work hours
    free_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))

    # Find the earliest free slot that can fit the meeting
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end), day)

    return None

# Input data
participants_schedules = [
    ["9:30 to 10:00", "12:30 to 13:00", "14:30 to 15:00", "16:30 to 17:00"],  # Adam
    ["10:00 to 11:00", "11:30 to 13:00", "13:30 to 14:30", "16:30 to 17:00"]   # Roy
]
work_hours_start = "9:00"
work_hours_end = "17:00"
duration_minutes = 30
day = "Monday"

# Find meeting time
result = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day)
if result:
    start_time, end_time, day = result
    print(f"{start_time}:{end_time}:{day}")
else:
    print("No suitable time found.")