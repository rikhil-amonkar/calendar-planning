def find_meeting_time(participants_schedules, day, work_hours, duration_minutes):
    start_hour, end_hour = work_hours
    total_minutes_in_day = (end_hour - start_hour) * 60
    time_slots = [True] * total_minutes_in_day  # True means available
    
    for person_schedule in participants_schedules:
        person_availability = [True] * total_minutes_in_day
        for busy_start, busy_end in person_schedule:
            # Convert hours to minutes (including fractional hours)
            busy_start_min = int((busy_start - start_hour) * 60)
            busy_end_min = int((busy_end - start_hour) * 60)
            for minute in range(busy_start_min, busy_end_min):
                if 0 <= minute < total_minutes_in_day:
                    person_availability[minute] = False
        
        for minute in range(total_minutes_in_day):
            time_slots[minute] &= person_availability[minute]
    
    duration_slots = duration_minutes
    for start_minute in range(total_minutes_in_day - duration_slots + 1):
        all_available = True
        for minute in range(start_minute, start_minute + duration_slots):
            if minute >= total_minutes_in_day or not time_slots[minute]:
                all_available = False
                break
        if all_available:
            start_time = start_hour + start_minute // 60
            start_min = start_minute % 60
            end_minute = start_minute + duration_slots
            end_time = start_hour + end_minute // 60
            end_min = end_minute % 60
            return (
                f"{start_time:02d}:{start_min:02d}-{end_time:02d}:{end_min:02d}",
                day
            )
    return None, None

# Define participants' schedules in hours (can include fractional hours)
participants_schedules = [
    [(9.0, 9.5), (10.0, 11.0), (12.0, 12.5)],  # Megan
    [(9.0, 9.5), (11.5, 12.0), (13.0, 14.0), (15.5, 16.5)],  # Christine
    [],  # Gabriel
    [(11.5, 12.0), (14.5, 15.0)],  # Sara
    [(9.5, 10.0), (10.5, 12.0), (12.5, 14.0), (14.5, 15.0), (15.5, 16.5)],  # Bruce
    [(10.0, 15.5), (16.0, 16.5)],  # Kathryn
    [(9.0, 9.5), (11.0, 11.5), (12.0, 14.0), (14.5, 15.5)],  # Billy
]

day = "Monday"
work_hours = (9, 17)  # 9:00 to 17:00
duration_minutes = 30

time_range, day = find_meeting_time(participants_schedules, day, work_hours, duration_minutes)
if time_range:
    print(f"{{{time_range}}} {day}")
else:
    print("No available time slot found")