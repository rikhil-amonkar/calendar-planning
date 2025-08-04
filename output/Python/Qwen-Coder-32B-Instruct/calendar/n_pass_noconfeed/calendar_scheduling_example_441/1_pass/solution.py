from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    current_time = start_time
    
    # Create a dictionary to store busy times for each participant
    busy_times = {}
    for name, times in participants.items():
        busy_times[name] = [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), t.split(" to "))) for t in times]
    
    # Iterate over each minute in the day to find available slots
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        slot_start = current_time
        slot_end = current_time + timedelta(minutes=meeting_duration)
        
        # Check if this slot is free for all participants
        is_free = True
        for name, times in busy_times.items():
            for busy_start, busy_end in times:
                if slot_start < busy_end and slot_end > busy_start:
                    is_free = False
                    break
            if not is_free:
                break
        
        if is_free:
            available_slots.append((slot_start, slot_end))
        
        current_time += timedelta(minutes=1)
    
    # Return the first available slot found
    if available_slots:
        return available_slots[0], "Monday"
    else:
        return None, None

# Define participants and their busy times
participants = {
    "Joan": ["11:30 to 12:00", "14:30 to 15:00"],
    "Megan": ["9:00 to 10:00", "14:00 to 14:30", "16:00 to 16:30"],
    "Austin": [],
    "Betty": ["9:30 to 10:00", "11:30 to 12:00", "13:30 to 14:00", "16:00 to 16:30"],
    "Judith": ["9:00 to 11:00", "12:00 to 13:00", "14:00 to 15:00"],
    "Terry": ["9:30 to 10:00", "11:30 to 12:30", "13:00 to 14:00", "15:00 to 15:30", "16:00 to 17:00"],
    "Kathryn": ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 13:00", "14:00 to 16:00", "16:30 to 17:00"]
}

# Define meeting duration and work hours
meeting_duration = 30  # in minutes
start_time = "9:00"
end_time = "17:00"

# Find a suitable meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, start_time, end_time)

# Output the result
if meeting_time:
    print(f"{meeting_time[0].strftime('%H:%M')}:{meeting_time[1].strftime('%H:%M')} {day_of_week}")
else:
    print("No available time found.")