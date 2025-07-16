from datetime import datetime, timedelta

def find_meeting_time(judith_schedule, timothy_schedule, meeting_duration, preferred_days, judith_avoid_monday, judith_avoid_wednesday_before_12):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    for day in preferred_days:
        judith_blocked_times = judith_schedule.get(day, [])
        timothy_blocked_times = timothy_schedule.get(day, [])
        
        if day == "Monday" and judith_avoid_monday:
            continue
        
        if day == "Wednesday":
            judith_blocked_times.append((datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")))
            if judith_avoid_wednesday_before_12:
                judith_blocked_times.append((datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")))
        
        current_time = work_start
        while current_time < work_end - timedelta(hours=meeting_duration):
            available = True
            for start, end in judith_blocked_times + timothy_blocked_times:
                if start <= current_time < end or start < current_time + timedelta(hours=meeting_duration) <= end:
                    available = False
                    current_time = end
                    break
            
            if available:
                meeting_start = current_time.strftime("%H:%M")
                meeting_end = (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M")
                return f"{meeting_start}:{meeting_end} {day}"
            
            current_time += timedelta(minutes=30)

judith_schedule = {
    "Monday": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))]
}

timothy_schedule = {
    "Monday": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tuesday": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Wednesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ]
}

meeting_duration = 1
preferred_days = ["Monday", "Tuesday", "Wednesday"]
judith_avoid_monday = True
judith_avoid_wednesday_before_12 = True

print(find_meeting_time(judith_schedule, timothy_schedule, meeting_duration, preferred_days, judith_avoid_monday, judith_avoid_wednesday_before_12))