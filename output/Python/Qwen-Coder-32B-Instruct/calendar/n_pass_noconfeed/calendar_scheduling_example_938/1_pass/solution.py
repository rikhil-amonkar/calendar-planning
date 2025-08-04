from datetime import datetime, timedelta

def find_meeting_time(eugene_schedule, eric_schedule, meeting_duration, preferred_avoid_day):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_timedelta = timedelta(minutes=meeting_duration)
    
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    for day in days_of_week:
        if day == preferred_avoid_day:
            continue
        
        eugene_busy_times = eugene_schedule.get(day, [])
        eric_busy_times = eric_schedule.get(day, [])
        
        all_busy_times = sorted(eugene_busy_times + eric_busy_times, key=lambda x: x[0])
        
        current_time = work_start
        while current_time < work_end:
            next_available_time = current_time
            
            for start, end in all_busy_times:
                if current_time < start:
                    next_available_time = current_time
                    break
                elif current_time < end:
                    current_time = end
                    break
            else:
                next_available_time = current_time
            
            potential_end_time = next_available_time + meeting_timedelta
            if potential_end_time <= work_end:
                return f"{next_available_time.strftime('%H:%M')}:{potential_end_time.strftime('%H:%M')}", day
            
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None, None

# Define schedules
eugene_schedule = {
    "Monday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Friday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))]
}

eric_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

meeting_duration = 30  # in minutes
preferred_avoid_day = "Wednesday"

time, day = find_meeting_time(eugene_schedule, eric_schedule, meeting_duration, preferred_avoid_day)
print(f"Meeting Time: {time}, Day: {day}")