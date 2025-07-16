from datetime import datetime, timedelta

def find_meeting_time(james_schedule, john_schedule, meeting_duration, work_start, work_end):
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(hours=meeting_duration)
    
    # Convert schedules to datetime objects
    james_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in james_schedule]
    john_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in john_schedule]
    
    # Find free times for both
    james_free_times = find_free_times(james_busy_times, work_start, work_end)
    john_free_times = find_free_times(john_busy_times, work_start, work_end)
    
    # Find common free time
    for j_start, j_end in james_free_times:
        for jo_start, jo_end in john_free_times:
            common_start = max(j_start, jo_start)
            common_end = min(j_end, jo_end)
            if common_end - common_start >= meeting_duration:
                return common_start.strftime("%H:%M"), common_end.strftime("%H:%M")

def find_free_times(busy_times, work_start, work_end):
    free_times = []
    current_start = work_start
    
    for start, end in busy_times:
        if start > current_start:
            free_times.append((current_start, start))
        current_start = max(current_start, end)
    
    if current_start < work_end:
        free_times.append((current_start, work_end))
    
    return free_times

# Schedules in the format of ("start", "end")
james_schedule = [("11:30", "12:00"), ("14:30", "15:00")]
john_schedule = [("9:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:30", "16:30")]

meeting_start, meeting_end = find_meeting_time(james_schedule, john_schedule, 1, "9:00", "17:00")
print(f"{meeting_start}:{meeting_end} Monday")