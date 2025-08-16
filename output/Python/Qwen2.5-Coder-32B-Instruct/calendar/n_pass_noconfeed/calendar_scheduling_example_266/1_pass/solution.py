from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert times to datetime objects for easier manipulation
    start = datetime.strptime(start_time, '%H:%M')
    end = datetime.strptime(end_time, '%H:%M')
    
    # Initialize available slots
    available_slots = []
    
    # Iterate over each minute in the workday to find common free slots
    current_time = start
    while current_time < end:
        slot_end = current_time + timedelta(minutes=meeting_duration)
        if slot_end > end:
            break
        
        # Check if this slot is free for all participants
        is_free_for_all = True
        for person_schedule in schedules.values():
            for busy_start, busy_end in person_schedule:
                busy_start_dt = datetime.strptime(busy_start, '%H:%M')
                busy_end_dt = datetime.strptime(busy_end, '%H:%M')
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < slot_end <= busy_end_dt:
                    is_free_for_all = False
                    break
            if not is_free_for_all:
                break
        
        if is_free_for_all:
            available_slots.append((current_time.strftime('%H:%M'), slot_end.strftime('%H:%M')))
        
        current_time += timedelta(minutes=1)
    
    return available_slots

# Define the schedules for each participant
schedules = {
    'Joe': [('09:30', '10:00'), ('10:30', '11:00')],
    'Keith': [('11:30', '12:00'), ('15:00', '15:30')],
    'Patricia': [('09:00', '09:30'), ('13:00', '13:30')],
    'Nancy': [('09:00', '11:00'), ('11:30', '16:30')],
    'Pamela': [('09:00', '10:00'), ('10:30', '11:00'), ('11:30', '12:30'), ('13:00', '14:00'), ('14:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')]
}

# Meeting details
meeting_duration = 30  # in minutes
start_time = '09:00'
end_time = '17:00'
day_of_week = 'Monday'

# Find available meeting times
available_slots = find_meeting_time(schedules, meeting_duration, start_time, end_time)

# Output the first available slot
if available_slots:
    print(f"{available_slots[0][0]}:{available_slots[0][1]} {day_of_week}")
else:
    print("No available time slots found.")