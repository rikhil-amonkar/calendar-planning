from datetime import datetime, timedelta

def find_meeting_time(james_schedule, john_schedule, meeting_duration, work_start, work_end):
    work_start_dt = datetime.strptime(work_start, "%H:%M")
    work_end_dt = datetime.strptime(work_end, "%H:%M")
    
    james_busy_times = [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), time.split(" to "))) for time in james_schedule]
    john_busy_times = [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), time.split(" to "))) for time in john_schedule]
    
    all_busy_times = sorted(james_busy_times + john_busy_times)
    
    current_time = work_start_dt
    while current_time < work_end_dt:
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
        
        meeting_end_time = next_available_time + timedelta(minutes=meeting_duration)
        if meeting_end_time <= work_end_dt:
            return next_available_time.strftime("%H:%M"), meeting_end_time.strftime("%H:%M")
        
        current_time += timedelta(minutes=15)  # Increment by 15 minutes to find the next slot

james_schedule = ["11:30 to 12:00", "14:30 to 15:00"]
john_schedule = ["9:30 to 11:00", "11:30 to 12:00", "12:30 to 13:30", "14:30 to 16:30"]
meeting_duration = 60  # in minutes
work_start = "09:00"
work_end = "17:00"

start_time, end_time = find_meeting_time(james_schedule, john_schedule, meeting_duration, work_start, work_end)
print(f"{start_time}:{end_time} Monday")