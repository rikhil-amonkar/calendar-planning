from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferred_start=None):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert busy times to datetime objects
    busy_times = {
        'Kimberly': [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                     (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                     (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
        'Megan': [],
        'Marie': [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
        'Diana': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("10:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
    }
    
    current_time = work_start
    while current_time + timedelta(minutes=meeting_duration) <= work_end:
        available = True
        for person in participants:
            for start, end in busy_times[person]:
                if start <= current_time < end or start < current_time + timedelta(minutes=meeting_duration) <= end:
                    available = False
                    break
            if not available:
                break
        
        if available and (preferred_start is None or current_time >= preferred_start):
            return current_time.strftime("%H:%M"), (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
        
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None

participants = ['Kimberly', 'Megan', 'Marie', 'Diana']
meeting_duration = 30  # in minutes
preferred_start = datetime.strptime("10:00", "%H:%M")  # Megan's preference

start_time, end_time = find_meeting_time(participants, meeting_duration, preferred_start)
print(f"{start_time}:{end_time} Monday")