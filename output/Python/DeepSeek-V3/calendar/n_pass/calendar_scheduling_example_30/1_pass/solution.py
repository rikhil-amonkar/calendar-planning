def find_meeting_time(participants_schedules, preferences, duration_minutes, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since start of day for easier comparison
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

    # Collect all busy intervals for each participant
    busy_intervals = []
    for participant, schedules in participents_schedules.items():
        for schedule in schedules:
            start, end = map(time_to_minutes, schedule.split(' to '))
            busy_intervals.append((start, end, participant))

    # Sort all intervals by start time
    busy_intervals_sorted = sorted(busy_intervals, key=lambda x: x[0])

    # Generate available slots by finding gaps between busy intervals
    available_slots = []
    prev_end = work_start
    for start, end, _ in busy_intervals_sorted:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Check each available slot for duration and preferences
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            # Check if slot fits duration and preferences
            meeting_end = slot_start + duration
            # Check Melissa's preference (not after 14:00)
            if "Melissa" in preferences:
                preference_time = time_to_minutes(preferences["Melissa"])
                if meeting_end > preference_time:
                    continue  # Skip slots that end after preferred time
            # Check if all participants are free during this slot
            all_free = True
            for participant in participents_schedules.keys():
                for start, end, p in busy_intervals:
                    if p == participant and not (meeting_end <= start or slot_start >= end):
                        all_free = False
                        break
                if not all_free:
                    break
            if all_free:
                return minutes_to_time(slot_start), minutes_to_time(meeting_end)
    return None, None

# Define the problem
participants_schedules = {
    "Jeffrey": ["9:30 to 10:00", "10:30 to 11:00"],
    "Virginia": ["9:00 to 9:30", "10:00 to 10:30", "14:30 to 15:00", "16:00 to 16:30"],
    "Melissa": ["9:00 to 11:30", "12:00 to 12:30", "13:00 to 15:00", "16:00 to 17:00"]
}

preferences = {"Melissa": "14:00"}  # Melissa prefers not to meet after 14:00
duration = 30  # minutes
work_hours_start = "9:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
start_time, end_time = find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end)

if start_time and end_time:
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")