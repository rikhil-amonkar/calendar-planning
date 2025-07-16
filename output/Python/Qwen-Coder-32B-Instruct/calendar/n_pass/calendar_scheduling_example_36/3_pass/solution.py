from datetime import datetime, timedelta

def find_meeting_time(availability, meeting_duration, day_of_week):
    # Convert availability to datetime objects
    start_of_day = datetime.strptime(f"09:00 {day_of_week}", "%H:%M %A")
    end_of_day = datetime.strptime(f"17:00 {day_of_week}", "%H:%M %A")  # Adjusted end_of_day to 17:00
    
    # Function to convert time string to datetime object
    def to_datetime(time_str):
        return datetime.strptime(f"{time_str} {day_of_week}", "%H:%M %A")
    
    # Initialize a list to store available time slots for each person
    available_slots_per_person = []
    
    # Iterate over each participant's schedule
    for person, schedule in availability.items():
        # Start with the beginning of the day
        current_start = start_of_day
        
        # Check each busy period
        for busy_start, busy_end in sorted(schedule):
            busy_start_dt = to_datetime(busy_start)
            busy_end_dt = to_datetime(busy_end)
            
            # If there's a gap between the current start and the busy start, add it as an available slot
            if busy_start_dt > current_start:
                available_slots_per_person.append((current_start, busy_start_dt))
            
            # Update the current start to the end of the busy period
            current_start = max(current_start, busy_end_dt)
        
        # Add the remaining time after the last busy period until the end of the day
        if current_start < end_of_day:
            available_slots_per_person.append((current_start, end_of_day))
    
    # Find common slots that work for all participants
    if not available_slots_per_person:
        return "No suitable time found"
    
    # Initialize common slots with the first person's available slots
    common_slots = available_slots_per_person
    
    # Intersect with each subsequent person's available slots
    for person_slots in available_slots_per_person[1:]:
        new_common_slots = []
        for common_slot in common_slots:
            for person_slot in person_slots:
                overlap_start = max(common_slot[0], person_slot[0])
                overlap_end = min(common_slot[1], person_slot[1])
                if overlap_start < overlap_end:
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots
        if not common_slots:
            return "No suitable time found"
    
    # Check if the common slot is large enough for the meeting
    for slot in common_slots:
        if (slot[1] - slot[0]).seconds >= meeting_duration * 3600:
            meeting_start = slot[0]
            meeting_end = meeting_start + timedelta(hours=meeting_duration)
            return f"{meeting_start.strftime('%H:%M')} - {meeting_end.strftime('%H:%M')} {day_of_week}"
    
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