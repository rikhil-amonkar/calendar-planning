from datetime import datetime, timedelta

def find_meeting_time(people_schedules, day, meeting_duration, constraints):
    start_of_day = datetime.strptime(f"{day} 09:00", "%A %H:%M")
    end_of_day = datetime.strptime(f"{day} 17:00", "%A %H:%M")
    current_time = start_of_day
    
    while current_time < end_of_day:
        available = True
        for person, schedule in people_schedules.items():
            for busy_start, busy_end in schedule:
                busy_start_dt = datetime.strptime(f"{day} {busy_start}", "%A %H:%M")
                busy_end_dt = datetime.strptime(f"{day} {busy_end}", "%A %H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    available = False
                    break
            if not available:
                break
        
        # Check constraints
        for constraint, value in constraints.items():
            if constraint == "before":
                if current_time >= datetime.strptime(f"{day} {value}", "%A %H:%M"):
                    available = False
                    break
        
        if available:
            meeting_end = current_time + timedelta(minutes=meeting_duration)
            return f"{current_time.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day
        
        current_time += timedelta(minutes=1)

# Define schedules and constraints
people_schedules = {
    "Emily": [("Monday 10:00", "Monday 10:30"), ("Monday 11:30", "Monday 12:30"), ("Monday 14:00", "Monday 15:00"), ("Monday 16:00", "Monday 16:30")],
    "Melissa": [("Monday 09:30", "Monday 10:00"), ("Monday 14:30", "Monday 15:00")],
    "Frank": [("Monday 10:00", "Monday 10:30"), ("Monday 11:00", "Monday 11:30"), ("Monday 12:30", "Monday 13:00"), ("Monday 13:30", "Monday 14:30"), ("Monday 15:00", "Monday 16:00"), ("Monday 16:30", "Monday 17:00")]
}

constraints = {
    "before": "Monday 16:00"
}

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(people_schedules, "Monday", 30, constraints)
print(meeting_time, meeting_day)