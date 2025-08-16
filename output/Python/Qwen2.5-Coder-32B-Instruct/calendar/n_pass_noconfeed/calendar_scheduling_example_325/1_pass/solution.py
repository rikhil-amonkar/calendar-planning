from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    current_time = start_time
    
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        available_slots.append(current_time)
        current_time += timedelta(minutes=15)  # Check every 15 minutes for better granularity
    
    # Find common available time slot
    common_slots = set(available_slots)
    
    for participant, busy_times in participants.items():
        busy_slots = set()
        for busy_start, busy_end in busy_times:
            busy_start = datetime.strptime(busy_start, "%H:%M")
            busy_end = datetime.strptime(busy_end, "%H:%M")
            current_busy = busy_start
            while current_busy < busy_end:
                busy_slots.add(current_busy)
                current_busy += timedelta(minutes=15)
        common_slots -= busy_slots
    
    # Return the first valid slot found
    if common_slots:
        meeting_start = min(common_slots)
        meeting_end = meeting_start + timedelta(minutes=meeting_duration)
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}, Monday"
    else:
        return "No common time slot found"

# Define participants' busy times
participants = {
    'Jose': [('11:00', '11:30'), ('12:30', '13:00')],
    'Keith': [('14:00', '14:30'), ('15:00', '15:30')],
    'Logan': [('9:00', '10:00'), ('12:00', '12:30'), ('15:00', '15:30')],
    'Megan': [('9:00', '10:30'), ('11:00', '12:00'), ('13:00', '13:30'), ('14:30', '16:30')],
    'Gary': [('9:00', '9:30'), ('10:00', '10:30'), ('11:30', '13:00'), ('13:30', '14:00'), ('14:30', '16:30')],
    'Bobby': [('11:00', '11:30'), ('12:00', '12:30'), ('13:00', '16:00')]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
start_time = "9:00"
end_time = "15:30"  # Jose's constraint

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, start_time, end_time))