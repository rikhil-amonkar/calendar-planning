from datetime import datetime, timedelta

def find_meeting_time():
    # Define the participants' busy schedules
    ryan_schedule = [
        ('Monday', (9, 30), (10, 0)),
        ('Monday', (11, 0), (12, 0)),
        ('Monday', (13, 0), (13, 30)),
        ('Monday', (15, 30), (16, 0)),
        ('Tuesday', (11, 30), (12, 30)),
        ('Tuesday', (15, 30), (16, 0)),
        ('Wednesday', (12, 0), (13, 0)),
        ('Wednesday', (15, 30), (16, 0)),
        ('Wednesday', (16, 30), (17, 0)),
    ]
    
    adam_schedule = [
        ('Monday', (9, 0), (10, 30)),
        ('Monday', (11, 0), (13, 30)),
        ('Monday', (14, 0), (16, 0)),
        ('Monday', (16, 30), (17, 0)),
        ('Tuesday', (9, 0), (10, 0)),
        ('Tuesday', (10, 30), (15, 30)),
        ('Tuesday', (16, 0), (17, 0)),
        ('Wednesday', (9, 0), (9, 30)),
        ('Wednesday', (10, 0), (11, 0)),
        ('Wednesday', (11, 30), (14, 30)),
        ('Wednesday', (15, 0), (15, 30)),
        ('Wednesday', (16, 0), (16, 30)),
    ]
    
    # Define the preferred meeting duration
    meeting_duration = timedelta(minutes=30)
    
    # Define the working hours and the days to check
    work_days = [('Monday', (9, 0), (17, 0)), 
                 ('Tuesday', (9, 0), (17, 0)), 
                 ('Wednesday', (9, 0), (17, 0))]
    
    # Check each day for available meeting time
    for day, start_hour, end_hour in work_days:
        start_time = datetime.strptime(f"{day} {start_hour[0]}:{start_hour[1]}", "%A %H:%M")
        end_time = datetime.strptime(f"{day} {end_hour[0]}:{end_hour[1]}", "%A %H:%M")
        
        # Create a busy time list
        busy_times = [(datetime.strptime(f"{d} {s[0]}:{s[1]}", "%A %H:%M"),
                       datetime.strptime(f"{d} {e[0]}:{e[1]}", "%A %H:%M")) 
                      for d, s, e in ryan_schedule + adam_schedule if d == day]
        
        # Check for free time slots
        current_time = start_time
        
        while current_time + meeting_duration <= end_time:
            meeting_end_time = current_time + meeting_duration
            
            # Check if the current time slot is busy
            if not any(busy_start < meeting_end_time and current_time < busy_end for busy_start, busy_end in busy_times):
                # Found a suitable time
                return f"{day}: {current_time.strftime('%H:%M')}:{meeting_end_time.strftime('%H:%M')}"
            
            # Increment current_time by a minute
            current_time += timedelta(minutes=1)

# Call the function and print the proposed time
meeting_time = find_meeting_time()
print(meeting_time)