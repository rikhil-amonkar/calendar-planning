import datetime

def find_meeting_time(schedules, duration="30:00"):
    all_free = []
    for person in schedules:
        free_times = []
        for time in person:
            if time[1] == True:
                free_times.append((time[0], time[1]))
        all_free.append(free_times)
    
    day_start = datetime.time(9, 0)
    day_end = datetime.time(17, 0)
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    for day in days:
        current_day = day_start
        while current_day <= day_end:
            end_time = datetime.time((current_day.hour + duration[0]) % 24, (current_day.minute + duration[1]) % 60)
            if end_time > day_end:
                current_day += datetime.timedelta(hours=1)
                continue
            
            conflict = False
            for person in all_free:
                for time in person:
                    if time[0] <= current_day < time[1]:
                        conflict = True
                        break
                if conflict:
                    break
            if conflict:
                current_day += datetime.timedelta(hours=1)
                continue
            
            for person in all_free:
                for time in person:
                    if time[0] <= end_time < time[1]:
                        conflict = True
                        break
                if conflict:
                    break
            if conflict:
                current_day += datetime.timedelta(hours=1)
                continue
            
            return f"{current_day.hour:02}:{current_day.minute:02}:{end_time.hour:02}:{end_time.minute:02} {day}"
            
            current_day += datetime.timedelta(hours=1)
    
    return "No suitable time found"

meeting_time = find_meeting_time([
    [ (datetime.time(9, 0), True) for _ in range(24*60) ],
    [ (datetime.time(9, 0), True) for _ in range(24*60) ],
    [ (datetime.time(9, 0), True) for _ in range(24*60) ],
    [
        (datetime.time(9, 0), True),
        (datetime.time(11, 0), False),
        (datetime.time(11, 30), False),
        (datetime.time(14, 30), False),
        (datetime.time(15, 0), False),
        (datetime.time(16, 0), False),
        (datetime.time(16, 30), False),
        (datetime.time(17, 0), False)
    ]
])