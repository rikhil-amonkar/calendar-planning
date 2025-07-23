def find_meeting_time(participants_schedules, day, work_hours, duration_minutes):
    start_hour, end_hour = work_hours
    total_minutes_in_day = int((end_hour - start_hour) * 60)  # Convert to integer
    time_slots = [True] * total_minutes_in_day

    for person, busy_slots in participants_schedules.items():
        for slot in busy_slots:
            start_slot = int((slot[0] - start_hour) * 60)  # Convert to integer
            end_slot = int((slot[1] - start_hour) * 60)    # Convert to integer
            for minute in range(start_slot, end_slot):
                if 0 <= minute < len(time_slots):  # Added bounds checking
                    time_slots[minute] = False

    duration_slots = duration_minutes
    for start_minute in range(len(time_slots) - duration_slots + 1):
        if all(time_slots[start_minute + i] for i in range(duration_slots)):
            start_time = start_hour + start_minute // 60
            start_minute_remainder = start_minute % 60
            end_time_minute = start_minute + duration_slots
            end_time = start_hour + end_time_minute // 60
            end_minute_remainder = end_time_minute % 60
            return (
                f"{int(start_time):02d}:{start_minute_remainder:02d}-"
                f"{int(end_time):02d}:{end_minute_remainder:02d}"
            )
    return None

participants_schedules = {
    "Judy": [(13.0, 13.5), (16.0, 16.5)],
    "Olivia": [(10.0, 10.5), (12.0, 13.0), (14.0, 14.5)],
    "Eric": [],
    "Jacqueline": [(10.0, 10.5), (15.0, 15.5)],
    "Laura": [(9.0, 10.0), (10.5, 12.0), (13.0, 13.5), (14.5, 15.0), (15.5, 17.0)],
    "Tyler": [(9.0, 10.0), (11.0, 11.5), (12.5, 13.0), (14.0, 14.5), (15.5, 17.0)],
    "Lisa": [(9.5, 10.5), (11.0, 11.5), (12.0, 12.5), (13.0, 13.5), (14.0, 14.5), (16.0, 17.0)],
}

day = "Monday"
work_hours = (9.0, 17.0)
duration_minutes = 30

meeting_time = find_meeting_time(participants_schedules, day, work_hours, duration_minutes)
print(f"{day}: {meeting_time}")