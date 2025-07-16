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

    # Collect all busy intervals from all participants
    all_busy = []
    for schedule in participants_schedules.values():
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            all_busy.append((start, end))

    # Sort all busy intervals by start time
    all_busy.sort()

    # Merge overlapping or adjacent busy intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:  # Overlapping or adjacent
                merged_busy[-1][1] = max(end, last_end)
            else:
                merged_busy.append([start, end])

    # Initialize the list of available slots
    available_slots = []

    # Check the time before the first busy interval
    if merged_busy:
        first_busy_start = merged_busy[0][0]
        if first_busy_start > work_start:
            available_start = work_start
            available_end = first_busy_start
            if available_end - available_start >= duration_min:
                available_slots.append((available_start, available_end))
    else:
        # No busy intervals at all - entire work day is available
        if work_end - work_start >= duration_min:
            return (minutes_to_time(work_start), 
                    minutes_to_time(work_start + duration_min))
        else:
            return None

    # Check gaps between busy intervals
    for i in range(len(merged_busy) - 1):
        current_end = merged_busy[i][1]
        next_start = merged_busy[i+1][0]
        if next_start - current_end >= duration_min:
            available_slots.append((current_end, next_start))

    # Check the time after the last busy interval
    last_busy_end = merged_busy[-1][1]
    if last_busy_end < work_end:
        available_start = last_busy_end
        available_end = work_end
        if available_end - available_start >= duration_min:
            available_slots.append((available_start, available_end))

    # Find the earliest available slot that fits the duration
    for slot_start, slot_end in available_slots:
        # Ensure the slot is within work hours
        actual_start = max(slot_start, work_start)
        actual_end = min(slot_end, work_end)
        if actual_end - actual_start >= duration_min:
            # Check if the slot is completely within work hours
            if actual_start >= work_start and actual_end <= work_end:
                return (minutes_to_time(actual_start), 
                        minutes_to_time(actual_start + duration_min))

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