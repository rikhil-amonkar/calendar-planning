def time_to_minutes(time_str):
    h, m = time_str.split(':')
    hours = int(h)
    minutes = int(m)
    total_minutes = (hours - 9) * 60 + minutes
    return total_minutes

group_busy = [False] * 480

danielle_schedule = "9:00 to 10:00, 10:30 to 11:00, 14:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00"
bruce_schedule = "11:00 to 11:30, 12:30 to 13:00, 14:00 to 14:30, 15:30 to 16:00"
eric_schedule = "9:00 to 9:30, 10:00 to 11:00, 11:30 to 13:00, 14:30 to 15:30"

schedules = [danielle_schedule, bruce_schedule, eric_schedule]

for schedule in schedules:
    meetings = schedule.split(',')
    for meeting in meetings:
        parts = meeting.split(' to ')
        if len(parts) < 2:
            continue
        start_str = parts[0].strip()
        end_str = parts[1].strip()
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        for minute in range(start_min, end_min):
            if minute < 480:
                group_busy[minute] = True

found_start = None
for start in range(0, 480 - 60 + 1):
    busy_found = False
    for i in range(start, start + 60):
        if group_busy[i]:
            busy_found = True
            break
    if not busy_found:
        found_start = start
        break

if found_start is None:
    print("No meeting time found")
else:
    start_hour = 9 + found_start // 60
    start_minute = found_start % 60
    end_minute_total = found_start + 60
    end_hour = 9 + end_minute_total // 60
    end_minute = end_minute_total % 60
    print("Monday")
    print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")