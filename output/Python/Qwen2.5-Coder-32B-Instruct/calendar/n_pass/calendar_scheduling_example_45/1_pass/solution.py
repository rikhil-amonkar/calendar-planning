from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert work hours to datetime objects
    work_start_dt = datetime.strptime(work_start, "%H:%M")
    work_end_dt = datetime.strptime(work_end, "%H:%M")
    
    # Initialize available slots
    available_slots = []
    
    # Check each participant's schedule
    for person, slots in schedules.items():
        current_time = work_start_dt
        for slot in slots:
            slot_start, slot_end = map(lambda x: datetime.strptime(x, "%H:%M"), slot)
            if current_time < slot_start:
                available_slots.append((current_time, slot_start))
            current_time = max(current_time, slot_end)
        if current_time < work_end_dt:
            available_slots.append((current_time, work_end_dt))
    
    # Find common available slots
    common_slots = available_slots[:]
    for i in range(1, len(schedules)):
        person_slots = schedules[list(schedules.keys())[i]]
        new_common_slots = []
        current_time = work_start_dt
        for slot in person_slots:
            slot_start, slot_end = map(lambda x: datetime.strptime(x, "%H:%M"), slot)
            for common_slot in common_slots:
                common_start, common_end = common_slot
                intersection_start = max(common_start, slot_start)
                intersection_end = min(common_end, slot_end)
                if intersection_start < intersection_end:
                    new_common_slots.append((intersection_start, intersection_end))
        common_slots = new_common_slots
    
    # Find a slot that fits the meeting duration
    for slot in common_slots:
        slot_start, slot_end = slot
        if (slot_end - slot_start) >= timedelta(minutes=meeting_duration):
            return slot_start.strftime("%H:%M"), (slot_start + timedelta(minutes=meeting_duration)).strftime("%H:%M")
    
    return None

# Define the schedules
schedules = {
    "Andrew": [],
    "Grace": [],
    "Samuel": [("09:00", "10:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")]
}

# Meeting details
meeting_duration = 30  # in minutes
work_start = "09:00"
work_end = "17:00"
day_of_week = "Monday"

# Find the meeting time
start_time, end_time = find_meeting_time(schedules, meeting_duration, work_start, work_end)

# Output the result
print(f"{start_time}:{end_time} {day_of_week}")