from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, day_of_week, start_time, end_time, constraints):
    # Convert times to datetime objects
    start_time = datetime.strptime(f"{day_of_week} {start_time}", "%A %H:%M")
    end_time = datetime.strptime(f"{day_of_week} {end_time}", "%A %H:%M")
    
    # Initialize available slots
    available_slots = []
    
    # Create a list of time slots from start to end time
    current_time = start_time
    while current_time < end_time:
        slot_end = current_time + timedelta(minutes=meeting_duration)
        if slot_end <= end_time:
            available_slots.append((current_time, slot_end))
        current_time += timedelta(minutes=1)
    
    # Filter slots based on individual schedules
    for person_schedule in schedules.values():
        for busy_start, busy_end in person_schedule:
            busy_start = datetime.strptime(busy_start, "%H:%M").replace(year=start_time.year, month=start_time.month, day=start_time.day)
            busy_end = datetime.strptime(busy_end, "%H:%M").replace(year=start_time.year, month=start_time.month, day=start_time.day)
            filtered_slots = []
            for slot_start, slot_end in available_slots:
                if slot_end <= busy_start or slot_start >= busy_end:
                    filtered_slots.append((slot_start, slot_end))
            available_slots = filtered_slots
    
    # Apply additional constraints
    final_slots = []
    for slot_start, slot_end in available_slots:
        valid = True
        for constraint_person, constraint_times in constraints.items():
            for constraint_start, constraint_end in constraint_times:
                constraint_start = datetime.strptime(constraint_start, "%H:%M").replace(year=start_time.year, month=start_time.month, day=start_time.day)
                constraint_end = datetime.strptime(constraint_end, "%H:%M").replace(year=start_time.year, month=start_time.month, day=start_time.day)
                if slot_end <= constraint_start or slot_start >= constraint_end:
                    continue
                else:
                    valid = False
                    break
            if not valid:
                break
        if valid:
            final_slots.append((slot_start, slot_end))
    
    # Output the first valid slot found
    if final_slots:
        slot_start, slot_end = final_slots[0]
        return f"{slot_start.strftime('%H:%M')} - {slot_end.strftime('%H:%M')} on {slot_start.strftime('%A')}"
    else:
        return "No available time slot found"

# Define schedules and constraints
schedules = {
    "Emily": [("10:00", "10:30"), ("11:30", "12:30"), ("14:00", "15:00"), ("16:00", "16:30")],
    "Melissa": [("9:30", "10:00"), ("14:30", "15:00")],
    "Frank": [("10:00", "10:30"), ("11:00", "11:30"), ("12:30", "13:00"), ("13:30", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")]
}

constraints = {
    "Frank": [("9:30", "17:00")]  # Frank does not want to meet after 9:30
}

# Meeting details
meeting_duration = 30  # in minutes
day_of_week = "Monday"
start_time = "9:00"
end_time = "17:00"

# Find and print the meeting time
print(find_meeting_time(schedules, meeting_duration, day_of_week, start_time, end_time, constraints))