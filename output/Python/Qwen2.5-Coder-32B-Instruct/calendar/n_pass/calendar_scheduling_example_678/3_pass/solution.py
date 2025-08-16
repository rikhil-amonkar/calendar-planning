from datetime import datetime, timedelta

def find_meeting_time(russell_schedule, alexander_schedule, preferred_start, meeting_duration):
    work_days = ['Monday', 'Tuesday']
    work_hours_start = 9
    work_hours_end = 17
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in work_days:
        russell_busy = russell_schedule.get(day, [])
        alexander_busy = alexander_schedule.get(day, [])
        
        # Combine and sort all busy times
        all_busy_times = sorted(russell_busy + alexander_busy, key=lambda x: x[0])
        
        # Set the starting time based on the day
        if day == 'Tuesday':
            current_time = datetime.strptime(f"{day} {preferred_start}:00", "%A %H:%M")
        else:
            current_time = datetime.strptime(f"{day} {work_hours_start}:00", "%A %H:%M")
        
        end_of_day = datetime.strptime(f"{day} {work_hours_end}:00", "%A %H:%M")
        
        while current_time < end_of_day:
            available = True
            meeting_end_time = current_time + meeting_duration
            
            for start, end in all_busy_times:
                busy_start = datetime.strptime(f"{day} {start}", "%A %H:%M")
                busy_end = datetime.strptime(f"{day} {end}", "%A %H:%M")
                
                if current_time < busy_end and meeting_end_time > busy_start:
                    available = False
                    current_time = busy_end
                    break
            
            if available:
                return current_time.strftime('%H:%M'), meeting_end_time.strftime('%H:%M'), day
            
            current_time += timedelta(minutes=30)  # Check every 30 minutes for availability
    
    return None, None, "No available time found"

# Schedules
russell_schedule = {
    'Monday': [('10:30', '11:00')],
    'Tuesday': [('13:00', '13:30')]
}

alexander_schedule = {
    'Monday': [('9:00', '11:30'), ('12:00', '14:30'), ('15:00', '17:00')],
    'Tuesday': [('9:00', '10:00'), ('13:00', '14:00'), ('15:00', '15:30'), ('16:00', '16:30')]
}

preferred_start_tuesday = 13  # 1 PM
meeting_duration_hours = 1

# Find and print the meeting time
meeting_start, meeting_end, meeting_day = find_meeting_time(russell_schedule, alexander_schedule, preferred_start_tuesday, meeting_duration_hours)

if meeting_day == "No available time found":
    print(meeting_day)
else:
    print(f"Meeting time: {meeting_start} - {meeting_end} on {meeting_day}")