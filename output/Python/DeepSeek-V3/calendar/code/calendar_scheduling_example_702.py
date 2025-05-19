from datetime import datetime, timedelta

def find_meeting_time(participants, days, work_hours_start, work_hours_end, duration, preferences):
    # Parse work hours
    start_hour, start_minute = map(int, work_hours_start.split(':'))
    end_hour, end_minute = map(int, work_hours_end.split(':'))
    
    # Convert duration to timedelta
    duration = timedelta(minutes=duration)
    
    for day in days:
        if day in preferences.get('avoid_days', []):
            continue
        
        # Initialize current time to start of work day
        current_time = datetime.strptime(f"{day} {work_hours_start}", "%A %H:%M")
        end_time = datetime.strptime(f"{day} {work_hours_end}", "%A %H:%M")
        
        while current_time + duration <= end_time:
            slot_end = current_time + duration
            slot_ok = True
            
            # Check each participant's availability
            for participant, meetings in participants.items():
                for meeting in meetings.get(day, []):
                    meeting_start = datetime.strptime(f"{day} {meeting[0]}", "%A %H:%M")
                    meeting_end = datetime.strptime(f"{day} {meeting[1]}", "%A %H:%M")
                    
                    # Check for overlap
                    if not (slot_end <= meeting_start or current_time >= meeting_end):
                        slot_ok = False
                        break
                
                if not slot_ok:
                    break
            
            if slot_ok:
                return day, current_time.time(), slot_end.time()
            
            # Move to next possible slot (in 15-minute increments for efficiency)
            current_time += timedelta(minutes=15)
    
    return None

# Define participants' schedules
participants = {
    "Robert": {
        "Monday": [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
        "Tuesday": [("10:30", "11:00"), ("15:00", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), 
                     ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")]
    },
    "Ralph": {
        "Monday": [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "11:30"), 
                    ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"), ("16:30", "17:00")]
    }
}

# Define meeting parameters
days_to_check = ["Monday", "Tuesday", "Wednesday"]
work_hours = ("9:00", "17:00")
meeting_duration = 30  # minutes
preferences = {
    "avoid_days": ["Monday"]  # Robert wants to avoid Monday
}

# Find meeting time
result = find_meeting_time(participants=participants,
                          days=days_to_check,
                          work_hours_start=work_hours[0],
                          work_hours_end=work_hours[1],
                          duration=meeting_duration,
                          preferences=preferences)

if result:
    day, start_time, end_time = result
    print(f"{day}:{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
else:
    print("No suitable time found.")