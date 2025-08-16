from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = set()
    
    # Create a time range from start to end time with 30 minute intervals
    current_time = start_time
    while current_time < end_time:
        available_slots.add(current_time)
        current_time += timedelta(minutes=30)
    
    # Remove unavailable times for each participant
    for person, busy_times in participants.items():
        for busy_start, busy_end in busy_times:
            busy_start = datetime.strptime(busy_start, "%H:%M")
            busy_end = datetime.strptime(busy_end, "%H:%M")
            
            current_busy_time = busy_start
            while current_busy_time < busy_end:
                if current_busy_time in available_slots:
                    available_slots.remove(current_busy_time)
                current_busy_time += timedelta(minutes=30)
    
    # Find a continuous slot of the required duration
    for slot in available_slots:
        potential_end_time = slot + timedelta(hours=meeting_duration)
        if all(slot + timedelta(minutes=i*30) in available_slots for i in range(meeting_duration * 2)):
            return f"{slot.strftime('%H:%M')}:{potential_end_time.strftime('%H:%M')}", "Monday"
    
    return None, None

# Define participants' schedules
participants = {
    'Julie': [('09:00', '09:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:30', '14:00'), ('16:00', '17:00')],
    'Sean': [('09:00', '09:30'), ('13:00', '13:30'), ('15:00', '15:30'), ('16:00', '16:30')],
    'Lori': [('10:00', '10:30'), ('11:00', '13:00'), ('15:30', '17:00')]
}

# Meeting details
meeting_duration = 1  # in hours
start_time = "09:00"
end_time = "17:00"

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, start_time, end_time)
print(f"{meeting_time}, {day_of_week}")