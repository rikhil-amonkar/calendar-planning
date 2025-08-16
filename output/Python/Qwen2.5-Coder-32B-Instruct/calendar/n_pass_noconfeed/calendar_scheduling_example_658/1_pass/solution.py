from datetime import datetime, timedelta

def find_meeting_time(shirley_schedule, albert_schedule, preferred_day, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=30)
    
    days = ["Monday", "Tuesday"]
    for day in days:
        shirley_busy_times = shirley_schedule.get(day, [])
        albert_busy_times = albert_schedule.get(day, [])
        
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            if day == preferred_day and current_time >= preferred_end_time:
                break
            
            available = True
            for busy_time in shirley_busy_times + albert_busy_times:
                if current_time < busy_time[1] and current_time + meeting_duration > busy_time[0]:
                    available = False
                    current_time = busy_time[1]
                    break
            
            if available:
                start_time_str = current_time.strftime("%H:%M")
                end_time_str = (current_time + meeting_duration).strftime("%H:%M")
                return f"{start_time_str}:{end_time_str} {day}"
            
            current_time += timedelta(minutes=15)

shirley_schedule = {
    "Monday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M"))]
}

albert_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

preferred_day = "Tuesday"
preferred_end_time = datetime.strptime("10:30", "%H:%M")

meeting_time = find_meeting_time(shirley_schedule, albert_schedule, preferred_day, preferred_end_time)
print(meeting_time)