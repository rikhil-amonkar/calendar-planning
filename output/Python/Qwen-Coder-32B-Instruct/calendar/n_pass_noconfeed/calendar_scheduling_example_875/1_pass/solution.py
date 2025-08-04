from datetime import datetime, timedelta

def find_meeting_time(natalie_schedule, william_schedule, meeting_duration, work_days):
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in work_days:
        natalie_busy = natalie_schedule[day]
        william_busy = william_schedule[day]
        
        natalie_free = find_free_times(natalie_busy)
        william_free = find_free_times(william_busy)
        
        common_free = find_common_free_times(natalie_free, william_free, meeting_duration)
        
        if common_free:
            start_time, end_time = common_free[0]
            return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, {day}"
    
    return "No common time found"

def find_free_times(busy_times):
    free_times = []
    start_of_day = datetime.strptime("09:00", "%H:%M")
    end_of_day = datetime.strptime("17:00", "%H:%M")
    
    current_start = start_of_day
    
    for start, end in busy_times:
        start = datetime.strptime(start, "%H:%M")
        end = datetime.strptime(end, "%H:%M")
        
        if start > current_start:
            free_times.append((current_start, start))
        
        current_start = max(current_start, end)
    
    if current_start < end_of_day:
        free_times.append((current_start, end_of_day))
    
    return free_times

def find_common_free_times(free_times_1, free_times_2, meeting_duration):
    common_free = []
    
    i, j = 0, 0
    
    while i < len(free_times_1) and j < len(free_times_2):
        start_1, end_1 = free_times_1[i]
        start_2, end_2 = free_times_2[j]
        
        common_start = max(start_1, start_2)
        common_end = min(end_1, end_2)
        
        if common_end - common_start >= meeting_duration:
            common_free.append((common_start, common_start + meeting_duration))
        
        if end_1 <= end_2:
            i += 1
        else:
            j += 1
    
    return common_free

natalie_schedule = {
    "Monday": [("09:00", "09:30"), ("10:00", "12:00"), ("12:30", "13:00"), ("14:00", "14:30"), ("15:00", "16:30")],
    "Tuesday": [("09:00", "09:30"), ("10:00", "10:30"), ("12:30", "14:00"), ("16:00", "17:00")],
    "Wednesday": [("11:00", "11:30"), ("16:00", "16:30")],
    "Thursday": [("10:00", "11:00"), ("11:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
}

william_schedule = {
    "Monday": [("09:30", "11:00"), ("11:30", "17:00")],
    "Tuesday": [("09:00", "13:00"), ("13:30", "16:00")],
    "Wednesday": [("09:00", "12:30"), ("13:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Thursday": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("15:00", "17:00")]
}

work_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
meeting_duration = 1

print(find_meeting_time(natalie_schedule, william_schedule, meeting_duration, work_days))