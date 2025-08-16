from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available slots for each participant
    available_slots = {}
    
    for participant, busy_times in participants.items():
        current_time = start
        available_slots[participant] = []
        
        while current_time < end:
            next_busy_start = end
            for busy_start, busy_end in busy_times:
                if current_time < busy_start:
                    next_busy_start = min(next_busy_start, busy_start)
            
            if next_busy_start - current_time >= timedelta(minutes=meeting_duration):
                available_slots[participant].append((current_time, current_time + timedelta(minutes=meeting_duration)))
            
            current_time = next_busy_start
    
    # Find common slots
    common_slots = available_slots[next(iter(available_slots))]
    for slots in available_slots.values():
        common_slots = [slot for slot in common_slots if slot in slots]
    
    # Return the first common slot found
    if common_slots:
        meeting_start, meeting_end = common_slots[0]
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", "Monday"
    else:
        return None, None

# Define participants' busy times
participants = {
    "Patrick": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Kayla": [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Carl": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
             (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Christian": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
start_time = "09:00"
end_time = "17:00"

# Find a suitable meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, start_time, end_time)
print(f"{meeting_time}, {day_of_week}")