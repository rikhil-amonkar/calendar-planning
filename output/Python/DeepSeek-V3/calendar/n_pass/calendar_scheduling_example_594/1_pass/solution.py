def find_meeting_time(participants_busy, work_hours_start, work_hours_end, duration_minutes, day):
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
    duration = duration_minutes

    # Collect all busy intervals for all participants
    all_busy = []
    for busy_slots in participants_busy.values():
        for slot in busy_slots:
            start, end = map(time_to_minutes, slot.split(' to '))
            all_busy.append((start, end))
    
    # Sort all busy intervals by start time
    all_busy.sort()

    # Find free slots by checking gaps between busy intervals and work hours
    free_slots = []
    prev_end = work_start

    for start, end in all_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))

    # Find the earliest free slot that can accommodate the meeting
    for slot in free_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (
                f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}",
                day
            )

    return None

# Define the problem parameters
participants_busy = {
    "Adam": [
        "09:30 to 10:00",
        "12:30 to 13:00",
        "14:30 to 15:00",
        "16:30 to 17:00"
    ],
    "Roy": [
        "10:00 to 11:00",
        "11:30 to 13:00",
        "13:30 to 14:30",
        "16:30 to 17:00"
    ]
}

work_hours_start = "09:00"
work_hours_end = "17:00"
duration_minutes = 30
day = "Monday"

# Find the meeting time
meeting_time, meeting_day = find_meeting_time(
    participants_busy=participants_busy,
    work_hours_start=work_hours_start,
    work_hours_end=work_hours_end,
    duration_minutes=duration_minutes,
    day=day
)

# Output the result
print(f"{meeting_time}:{meeting_day}")