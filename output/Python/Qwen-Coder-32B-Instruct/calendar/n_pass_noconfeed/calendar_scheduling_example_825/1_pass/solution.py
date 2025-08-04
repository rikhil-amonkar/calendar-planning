from datetime import datetime, timedelta

def find_meeting_time(laura_schedule, philip_schedule, meeting_duration, days):
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in days:
        laura_busy_times = laura_schedule.get(day, [])
        philip_busy_times = philip_schedule.get(day, [])
        
        laura_free_times = []
        philip_free_times = []
        
        start_of_day = datetime.strptime(f"{day} 09:00", "%A %H:%M")
        end_of_day = datetime.strptime(f"{day} 17:00", "%A %H:%M")
        
        # Calculate Laura's free times
        current_start = start_of_day
        for busy_start, busy_end in laura_busy_times:
            busy_start = datetime.strptime(f"{day} {busy_start}", "%A %H:%M")
            busy_end = datetime.strptime(f"{day} {busy_end}", "%A %H:%M")
            if current_start < busy_start:
                laura_free_times.append((current_start, busy_start))
            current_start = busy_end
        if current_start < end_of_day:
            laura_free_times.append((current_start, end_of_day))
        
        # Calculate Philip's free times
        current_start = start_of_day
        for busy_start, busy_end in philip_busy_times:
            busy_start = datetime.strptime(f"{day} {busy_start}", "%A %H:%M")
            busy_end = datetime.strptime(f"{day} {busy_end}", "%A %H:%M")
            if current_start < busy_start:
                philip_free_times.append((current_start, busy_start))
            current_start = busy_end
        if current_start < end_of_day:
            philip_free_times.append((current_start, end_of_day))
        
        # Find common free times
        for laura_start, laura_end in laura_free_times:
            for philip_start, philip_end in philip_free_times:
                common_start = max(laura_start, philip_start)
                common_end = min(laura_end, philip_end)
                if common_start + meeting_duration <= common_end:
                    return common_start.strftime("%H:%M"), common_end.strftime("%H:%M"), day

# Define schedules
laura_schedule = {
    "Monday": [("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Tuesday": [("9:30", "10:00"), ("11:00", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")],
    "Wednesday": [("11:30", "12:00"), ("12:30", "13:00"), ("15:30", "16:30")],
    "Thursday": [("10:30", "11:00"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]
}

philip_schedule = {
    "Monday": [("9:00", "17:00")],
    "Tuesday": [("9:00", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
    "Wednesday": [("9:00", "10:00"), ("11:00", "12:00"), ("12:30", "16:00"), ("16:30", "17:00")],
    "Thursday": [("9:00", "10:30"), ("11:00", "12:30"), ("13:00", "17:00")]
}

# Days to consider
days = ["Monday", "Tuesday", "Thursday"]

# Find and print the meeting time
start_time, end_time, day = find_meeting_time(laura_schedule, philip_schedule, 1, days)
print(f"{start_time}:{end_time} {day}")