from datetime import datetime, timedelta

def find_meeting_time(cheryl_schedule, kyle_schedule, meeting_duration, available_days):
    meeting_duration = timedelta(minutes=meeting_duration)
    
    for day in available_days:
        cheryl_busy_times = cheryl_schedule.get(day, [])
        kyle_busy_times = kyle_schedule.get(day, [])
        
        cheryl_free_times = get_free_times(cheryl_busy_times, 9, 17)
        kyle_free_times = get_free_times(kyle_busy_times, 9, 17)
        
        common_free_times = find_common_free_times(cheryl_free_times, kyle_free_times)
        
        for start, end in common_free_times:
            if end - start >= meeting_duration:
                meeting_start = start.strftime("%H:%M")
                meeting_end = (start + meeting_duration).strftime("%H:%M")
                return f"{meeting_start}:{meeting_end} {day}"
    
    return "No suitable time found"

def get_free_times(busy_times, start_hour, end_hour):
    current_time = datetime.strptime(f"01/01/2023 {start_hour}:00", "%d/%m/%Y %H:%M")
    end_time = datetime.strptime(f"01/01/2023 {end_hour}:00", "%d/%m/%Y %H:%M")
    free_times = []
    
    for busy_start, busy_end in sorted(busy_times):
        busy_start_dt = datetime.strptime(f"01/01/2023 {busy_start}", "%d/%m/%Y %H:%M")
        busy_end_dt = datetime.strptime(f"01/01/2023 {busy_end}", "%d/%m/%Y %H:%M")
        
        if current_time < busy_start_dt:
            free_times.append((current_time, busy_start_dt))
        
        current_time = max(current_time, busy_end_dt)
    
    if current_time < end_time:
        free_times.append((current_time, end_time))
    
    return free_times

def find_common_free_times(cheryl_free_times, kyle_free_times):
    common_free_times = []
    i, j = 0, 0
    
    while i < len(cheryl_free_times) and j < len(kyle_free_times):
        cheryl_start, cheryl_end = cheryl_free_times[i]
        kyle_start, kyle_end = kyle_free_times[j]
        
        common_start = max(cheryl_start, kyle_start)
        common_end = min(cheryl_end, kyle_end)
        
        if common_start < common_end:
            common_free_times.append((common_start, common_end))
        
        if cheryl_end <= kyle_end:
            i += 1
        else:
            j += 1
    
    return common_free_times

cheryl_schedule = {
    'Monday': [('09:00', '09:30'), ('11:30', '13:00'), ('15:30', '16:00')],
    'Tuesday': [('15:00', '15:30')]
}

kyle_schedule = {
    'Monday': [('09:00', '17:00')],
    'Tuesday': [('09:30', '17:00')],
    'Wednesday': [('09:00', '09:30'), ('10:00', '13:00'), ('13:30', '14:00'), ('14:30', '17:00')]
}

available_days = ['Monday', 'Tuesday']
meeting_duration = 30

print(find_meeting_time(cheryl_schedule, kyle_schedule, meeting_duration, available_days))