from datetime import datetime, timedelta

def find_meeting_time(availability, meeting_duration, day_of_week):
    # Convert availability to datetime objects
    start_of_day = datetime.strptime(f"09:00 {day_of_week}", "%H:%M %A")
    end_of_day = datetime.strptime(f"17:00 {day_of_week}", "%H:%M %A")
    
    # Initialize a list to store available time slots
    available_slots = []
    
    # Iterate over each participant's schedule
    for person, schedule in availability.items():
        # Start with the beginning of the day
        current_start = start_of_day
        
        # Check each busy period
        for busy_start, busy_end in sorted(schedule):
            busy_start_dt = datetime.strptime(f"{busy_start} {day_of_week}", "%H:%M %A")
            busy_end_dt = datetime.strptime(f"{busy_end} {day_of_week}", "%H:%M %A")
            
            # If there's a gap between the current start and the busy start, add it as an available slot
            if busy_start_dt > current_start:
                available_slots.append((current_start, busy_start_dt))
            
            # Update the current start to the end of the busy period
            current_start = max(current_start, busy_end_dt)
        
        # Add the remaining time after the last busy period until the end of the day
        if current_start < end_of_day:
            available_slots.append((current_start, end_of_day))
    
    # Find a common slot that works for all participants and fits the meeting duration
    common_slots = available_slots[0]
    for slot in available_slots[1:]:
        common_slots = (max(common_slots[0], slot[0]), min(common_slots[1], slot[1]))
    
    # Check if the common slot is large enough for the meeting
    if (common_slots[1] - common_slots[0]).seconds >= meeting_duration * 3600:
        meeting_start = common_slots[0]
        meeting_end = meeting_start + timedelta(hours=meeting_duration)
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} {day_of_week}"
    else:
        return "No suitable time found"

# Define availability
availability = {
    'Ryan': [('09:00', '09:30'), ('12:30', '13:00')],
    'Ruth': [],
    'Denise': [('09:30', '10:30'), ('12:00', '13:00'), ('14:30', '16:30')]
}

# Meeting duration in hours
meeting_duration = 1

# Day of the week
day_of_week = "Monday"

# Find and print the meeting time
print(find_meeting_time(availability, meeting_duration, day_of_week))