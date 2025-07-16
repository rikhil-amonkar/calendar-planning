from datetime import datetime, timedelta

def find_meeting_time(danielle_schedule, bruce_schedule, eric_schedule, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    current_time = work_start
    
    while current_time < work_end - timedelta(hours=meeting_duration):
        current_slot_end = current_time + timedelta(hours=meeting_duration)
        current_slot = (current_time.time(), current_slot_end.time())
        
        # Check if the current slot is available for all three
        if (not any(slot[0] <= current_slot[0] < slot[1] or slot[0] < current_slot[1] <= slot[1]
                   for slot in danielle_schedule) and
            not any(slot[0] <= current_slot[0] < slot[1] or slot[0] < current_slot[1] <= slot[1]
                    for slot in bruce_schedule) and
            not any(slot[0] <= current_slot[0] < slot[1] or slot[0] < current_slot[1] <= slot[1]
                    for slot in eric_schedule)):
            return current_time.strftime("%H:%M"), current_slot_end.strftime("%H:%M")
        
        current_time += timedelta(minutes=30)  # Check every 30 minutes

# Define the schedules as lists of tuples (start_time, end_time)
danielle_schedule = [
    (datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("10:00", "%H:%M").time()),
    (datetime.strptime("10:30", "%H:%M").time(), datetime.strptime("11:00", "%H:%M").time()),
    (datetime.strptime("14:30", "%H:%M").time(), datetime.strptime("15:00", "%H:%M").time()),
    (datetime.strptime("15:30", "%H:%M").time(), datetime.strptime("16:00", "%H:%M").time()),
    (datetime.strptime("16:30", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())
]

bruce_schedule = [
    (datetime.strptime("11:00", "%H:%M").time(), datetime.strptime("11:30", "%H:%M").time()),
    (datetime.strptime("12:30", "%H:%M").time(), datetime.strptime("13:00", "%H:%M").time()),
    (datetime.strptime("14:00", "%H:%M").time(), datetime.strptime("14:30", "%H:%M").time()),
    (datetime.strptime("15:30", "%H:%M").time(), datetime.strptime("16:00", "%H:%M").time())
]

eric_schedule = [
    (datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("09:30", "%H:%M").time()),
    (datetime.strptime("10:00", "%H:%M").time(), datetime.strptime("11:00", "%H:%M").time()),
    (datetime.strptime("11:30", "%H:%M").time(), datetime.strptime("13:00", "%H:%M").time()),
    (datetime.strptime("14:30", "%H:%M").time(), datetime.strptime("15:30", "%H:%M").time())
]

meeting_duration = 1  # Meeting duration in hours
start_time, end_time = find_meeting_time(danielle_schedule, bruce_schedule, eric_schedule, meeting_duration)
print(f"{start_time}-{end_time} Monday")