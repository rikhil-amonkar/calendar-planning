from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Create a list of available time slots
    available_slots = [(work_start, work_end)]
    
    # Update the available slots based on each participant's schedule
    for participant in participants:
        busy_times = participant['busy_times']
        new_available_slots = []
        
        for start, end in available_slots:
            current_start = start
            
            for busy_start, busy_end in busy_times:
                if current_start < busy_start:
                    new_available_slots.append((current_start, busy_start))
                current_start = max(current_start, busy_end)
            
            if current_start < end:
                new_available_slots.append((current_start, end))
        
        available_slots = new_available_slots
    
    # Find a suitable time slot that fits the meeting duration
    for start, end in available_slots:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            return meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M"), meeting_start.strftime("%A")
    
    return None

# Define participant schedules
participants = [
    {'name': 'Andrea', 'busy_times': []},
    {'name': 'Jack', 'busy_times': [(datetime.strptime("09:00", "%H:%M"), 
                                       datetime.strptime("09:30", "%H:%M")),
                                      (datetime.strptime("14:00", "%H:%M"), 
                                       datetime.strptime("14:30", "%H:%M"))]},
    {'name': 'Madison', 'busy_times': [(datetime.strptime("09:30", "%H:%M"), 
                                          datetime.strptime("10:30", "%H:%M")),
                                         (datetime.strptime("13:00", "%H:%M"), 
                                          datetime.strptime("14:00", "%H:%M")),
                                         (datetime.strptime("15:00", "%H:%M"), 
                                          datetime.strptime("15:30", "%H:%M")),
                                         (datetime.strptime("16:30", "%H:%M"), 
                                          datetime.strptime("17:00", "%H:%M"))]},
    {'name': 'Rachel', 'busy_times': [(datetime.strptime("09:30", "%H:%M"), 
                                         datetime.strptime("10:30", "%H:%M")),
                                        (datetime.strptime("11:00", "%H:%M"), 
                                         datetime.strptime("11:30", "%H:%M")),
                                        (datetime.strptime("12:00", "%H:%M"), 
                                         datetime.strptime("13:30", "%H:%M")),
                                        (datetime.strptime("14:30", "%H:%M"), 
                                         datetime.strptime("15:30", "%H:%M")),
                                        (datetime.strptime("16:00", "%H:%M"), 
                                         datetime.strptime("17:00", "%H:%M"))]},
    {'name': 'Douglas', 'busy_times': [(datetime.strptime("09:00", "%H:%M"), 
                                          datetime.strptime("11:30", "%H:%M")),
                                         (datetime.strptime("12:00", "%H:%M"), 
                                          datetime.strptime("16:30", "%H:%M"))]},
    {'name': 'Ryan', 'busy_times': [(datetime.strptime("09:00", "%H:%M"), 
                                       datetime.strptime("09:30", "%H:%M")),
                                      (datetime.strptime("13:00", "%H:%M"), 
                                       datetime.strptime("14:00", "%H:%M")),
                                      (datetime.strptime("14:30", "%H:%M"), 
                                       datetime.strptime("17:00", "%H:%M"))]},
]

# Meeting duration of 30 minutes
meeting_duration = timedelta(minutes=30)

# Find and print the meeting time
start_time, end_time, day = find_meeting_time(participants, meeting_duration)
print(f"{start_time}:{end_time}:{day}")