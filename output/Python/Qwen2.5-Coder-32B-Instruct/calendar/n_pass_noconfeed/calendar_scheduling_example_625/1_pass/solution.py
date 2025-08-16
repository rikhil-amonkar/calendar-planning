from datetime import datetime, timedelta

def find_meeting_time(jeffrey_schedule, harold_schedule, meeting_duration, preferred_days, harold_avoid_day):
    meeting_duration = timedelta(minutes=meeting_duration)
    
    for day in preferred_days:
        if day == harold_avoid_day:
            continue
        
        harold_free_slots = []
        start_of_day = datetime.strptime(f"{day} 09:00", "%A %H:%M")
        end_of_day = datetime.strptime(f"{day} 17:00", "%A %H:%M")
        
        previous_end = start_of_day
        for event in harold_schedule[day]:
            event_start = datetime.strptime(f"{day} {event[0]}", "%A %H:%M")
            event_end = datetime.strptime(f"{day} {event[1]}", "%A %H:%M")
            
            if previous_end < event_start:
                harold_free_slots.append((previous_end, event_start))
            
            previous_end = max(previous_end, event_end)
        
        if previous_end < end_of_day:
            harold_free_slots.append((previous_end, end_of_day))
        
        for slot in harold_free_slots:
            if slot[1] - slot[0] >= meeting_duration:
                meeting_start = slot[0]
                meeting_end = meeting_start + meeting_duration
                return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day
    
    return None, None

jeffrey_schedule = {
    "Monday": [],
    "Tuesday": []
}

harold_schedule = {
    "Monday": [("09:00", "10:00"), ("10:30", "17:00")],
    "Tuesday": [("09:00", "09:30"), ("10:30", "11:30"), ("12:30", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")]
}

meeting_duration = 30
preferred_days = ["Monday", "Tuesday"]
harold_avoid_day = "Monday"

meeting_time, meeting_day = find_meeting_time(jeffrey_schedule, harold_schedule, meeting_duration, preferred_days, harold_avoid_day)
print(f"{meeting_time}:{meeting_day}")