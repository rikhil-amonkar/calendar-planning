from datetime import datetime, timedelta

def find_meeting_time(arthur_schedule, michael_schedule, unavailable_days, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    days = ["Monday", "Tuesday", "Wednesday"]
    
    for day in days:
        if day in unavailable_days:
            continue
        
        arthur_meetings = arthur_schedule.get(day, [])
        michael_meetings = michael_schedule.get(day, [])
        
        arthur_free_times = get_free_times(arthur_meetings, work_start, work_end)
        michael_free_times = get_free_times(michael_meetings, work_start, work_end)
        
        common_free_times = find_common_free_times(arthur_free_times, michael_free_times)
        
        for start, end in common_free_times:
            if (end - start) >= timedelta(minutes=meeting_duration):
                return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}", day
    
    return None, None

def get_free_times(meetings, work_start, work_end):
    free_times = []
    current_time = work_start
    
    for meeting in meetings:
        meeting_start, meeting_end = meeting
        if current_time < meeting_start:
            free_times.append((current_time, meeting_start))
        current_time = max(current_time, meeting_end)
    
    if current_time < work_end:
        free_times.append((current_time, work_end))
    
    return free_times

def find_common_free_times(arthur_free_times, michael_free_times):
    common_free_times = []
    i, j = 0, 0
    
    while i < len(arthur_free_times) and j < len(michael_free_times):
        arthur_start, arthur_end = arthur_free_times[i]
        michael_start, michael_end = michael_free_times[j]
        
        common_start = max(arthur_start, michael_start)
        common_end = min(arthur_end, michael_end)
        
        if common_start < common_end:
            common_free_times.append((common_start, common_end))
        
        if arthur_end <= michael_end:
            i += 1
        else:
            j += 1
    
    return common_free_times

arthur_schedule = {
    "Monday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

michael_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))]
}

unavailable_days = ["Tuesday"]
meeting_duration = 30

time, day = find_meeting_time(arthur_schedule, michael_schedule, unavailable_days, meeting_duration)
print(f"Meeting time: {time}, Day: {day}")