def find_meeting_time(participants_schedules, day, work_hours, duration_minutes):
    start_hour, end_hour = work_hours
    total_minutes_in_day = (end_hour - start_hour) * 60
    time_slots = [True] * total_minutes_in_day  # True means available

    for minute in range(total_minutes_in_day):
        current_time = start_hour * 60 + minute
        current_hour = current_time // 60
        current_minute = current_time % 60

        for person, busy_slots in participants_schedules.items():
            for busy_start, busy_end in busy_slots:
                busy_start_min = busy_start[0] * 60 + busy_start[1]
                busy_end_min = busy_end[0] * 60 + busy_end[1]
                if busy_start_min <= current_time < busy_end_min:
                    time_slots[minute] = False
                    break

    duration_slots = duration_minutes
    for start_minute in range(len(time_slots) - duration_slots + 1):
        all_available = True
        for i in range(duration_slots):
            if not time_slots[start_minute + i]:
                all_available = False
                break
        if all_available:
            start_time = start_hour * 60 + start_minute
            end_time = start_time + duration_slots
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    return None

def parse_schedule(schedule_str):
    schedule = []
    for busy_str in schedule_str.split('; '):
        if not busy_str:
            continue
        parts = busy_str.split(' to ')
        start_time = parts[0].split(':')
        end_time = parts[1].split(':')
        start = (int(start_time[0]), int(start_time[1]))
        end = (int(end_time[0]), int(end_time[1]))
        schedule.append((start, end))
    return schedule

participants = {
    "Patrick": parse_schedule("9:00 to 9:30; 10:00 to 10:30; 13:30 to 14:00; 16:00 to 16:30"),
    "Kayla": parse_schedule("12:30 to 13:30; 15:00 to 15:30; 16:00 to 16:30"),
    "Carl": parse_schedule("10:30 to 11:00; 12:00 to 12:30; 13:00 to 13:30; 14:30 to 17:00"),
    "Christian": parse_schedule("9:00 to 12:30; 13:00 to 14:00; 14:30 to 17:00")
}

day = "Monday"
work_hours = (9, 17)  # 9:00 to 17:00
duration_minutes = 30

meeting_time = find_meeting_time(participants, day, work_hours, duration_minutes)
print(f"{day}: {meeting_time}")