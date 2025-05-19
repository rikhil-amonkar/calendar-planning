from datetime import datetime, timedelta

# Function to find a suitable meeting time
def find_meeting_time(participants, duration, day_of_week):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Create a list of busy slots from participants
    busy_slots = []
    for schedule in participants.values():
        for busy in schedule:
            busy_slots.append((datetime.strptime(busy[0], "%H:%M"), datetime.strptime(busy[1], "%H:%M")))
    
    # Check for potential meeting slots
    time_slot = work_start
    while time_slot + duration <= work_end:
        end_time_slot = time_slot + duration
        if all(not (start < end_time_slot and end > time_slot) for start, end in busy_slots):
            return f"{time_slot.strftime('%H:%M')}:{end_time_slot.strftime('%H:%M')}", day_of_week
        time_slot += timedelta(minutes=1)
    
    return None

# Participants' busy times
participants = {
    'Jacob': [('13:30', '14:00'), ('14:30', '15:00')],
    'Diana': [('09:30', '10:00'), ('11:30', '12:00'), ('13:00', '13:30'), ('16:00', '16:30')],
    'Adam': [('09:30', '10:30'), ('11:00', '12:30'), ('15:30', '16:00')],
    'Angela': [('09:30', '10:00'), ('10:30', '12:00'), ('13:00', '15:30'), ('16:00', '16:30')],
    'Dennis': [('09:00', '09:30'), ('10:30', '11:30'), ('13:00', '15:00'), ('16:30', '17:00')],
}

# Meeting duration
duration = timedelta(minutes=30)
day_of_week = "Monday"

# Find and print the meeting time
meeting_time = find_meeting_time(participants, duration, day_of_week)
print(meeting_time)