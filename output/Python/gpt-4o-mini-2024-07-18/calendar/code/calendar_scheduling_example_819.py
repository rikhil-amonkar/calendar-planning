from datetime import datetime, timedelta

# Participants' availability
julie_schedule = []
ruth_schedule = [
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),  # Monday
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),  # Tuesday
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),  # Wednesday
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),  # Thursday busy
    (datetime.strptime('11:30', '%H:%M'), datetime.strptime('14:30', '%H:%M')),  # Thursday busy
    (datetime.strptime('15:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))   # Thursday busy
]

# Meeting constraints
meeting_duration = timedelta(minutes=30)
work_hours_start = datetime.strptime('09:00', '%H:%M')
work_hours_end = datetime.strptime('17:00', '%H:%M')
days_of_week = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Function to find a suitable meeting time
def find_meeting_time():
    for day in days_of_week:
        for start_hour in range(work_hours_start.hour, work_hours_end.hour):
            proposed_start = datetime.strptime(f'{day} {start_hour:02}:00', '%A %H:%M')
            proposed_end = proposed_start + meeting_duration
            
            if proposed_end.time() > work_hours_end.time():
                continue
            
            if day == 'Thursday' and proposed_end <= datetime.strptime('11:30', '%H:%M'):
                continue
            
            if proposed_start.time() < work_hours_start.time() or proposed_end.time() > work_hours_end.time():
                continue
            
            # Check Ruth's schedule
            slot_available = True
            for busy_start, busy_end in ruth_schedule:
                if not (proposed_end <= busy_start or proposed_start >= busy_end):
                    slot_available = False
                    break
            
            if slot_available:
                return proposed_start.time(), proposed_end.time(), day
    
    return None

# Get the meeting time
meeting_time = find_meeting_time()
if meeting_time:
    start_time, end_time, meeting_day = meeting_time
    print(f'{start_time.strftime("%H:%M")} : {end_time.strftime("%H:%M")}, {meeting_day}')