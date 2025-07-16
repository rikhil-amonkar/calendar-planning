from datetime import datetime, timedelta

def find_meeting_time(laura_schedule, philip_schedule, meeting_duration, days):
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in days:
        laura_busy = laura_schedule.get(day, [])
        philip_busy = philip_schedule.get(day, [])
        
        laura_free = []
        philip_free = []
        
        start_of_day = datetime.strptime(f"{day} 09:00", "%A %H:%M")
        end_of_day = datetime.strptime(f"{day} 17:00", "%A %H:%M")
        
        # Calculate free slots for Laura
        current_time = start_of_day
        for busy_slot in laura_busy:
            busy_start, busy_end = [datetime.strptime(f"{day} {time}", "%A %H:%M") for time in busy_slot]
            if current_time < busy_start:
                laura_free.append((current_time, busy_start))
            current_time = max(current_time, busy_end)
        if current_time < end_of_day:
            laura_free.append((current_time, end_of_day))
        
        # Calculate free slots for Philip
        current_time = start_of_day
        for busy_slot in philip_busy:
            busy_start, busy_end = [datetime.strptime(f"{day} {time}", "%A %H:%M") for time in busy_slot]
            if current_time < busy_start:
                philip_free.append((current_time, busy_start))
            current_time = max(current_time, busy_end)
        if current_time < end_of_day:
            philip_free.append((current_time, end_of_day))
        
        # Find common free slots
        for laura_slot in laura_free:
            for philip_slot in philip_free:
                common_start = max(laura_slot[0], philip_slot[0])
                common_end = min(laura_slot[1], philip_slot[1])
                if common_end - common_start >= meeting_duration:
                    return f"{common_start.strftime('%H:%M')}:{(common_start + meeting_duration).strftime('%H:%M')}", day
    
    return None, None

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

# Constraints
meeting_duration = 1  # in hours
days = ["Monday", "Tuesday", "Thursday"]  # Philip can't meet on Wednesday

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(laura_schedule, philip_schedule, meeting_duration, days)

print(f"Meeting Time: {meeting_time}, Day: {meeting_day}")