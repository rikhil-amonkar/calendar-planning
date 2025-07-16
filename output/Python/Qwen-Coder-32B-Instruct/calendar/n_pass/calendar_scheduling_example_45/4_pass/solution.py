from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert work hours to datetime objects
    work_start_dt = datetime.strptime(work_start, "%H:%M")
    work_end_dt = datetime.strptime(work_end, "%H:%M")
    
    # Function to convert time string to datetime object
    def to_datetime(time_str):
        return datetime.strptime(time_str, "%H:%M")
    
    # Initialize available slots for each person
    available_slots = {}
    for person, slots in schedules.items():
        person_slots = []
        current_time = work_start_dt
        for slot in slots:
            slot_start, slot_end = map(to_datetime, slot)
            if current_time < slot_start:
                person_slots.append((current_time, slot_start))
            current_time = max(current_time, slot_end)
        if current_time < work_end_dt:
            person_slots.append((current_time, work_end_dt))
        available_slots[person] = person_slots
    
    # Find common available slots
    common_slots = available_slots[list(schedules.keys())[0]]
    for person, slots in available_slots.items():
        new_common_slots = []
        for slot in slots:
            slot_start, slot_end = slot
            for common_slot in common_slots:
                common_start, common_end = common_slot
                intersection_start = max(common_start, slot_start)
                intersection_end = min(common_end, slot_end)
                if intersection_start < intersection_end:
                    new_common_slots.append((intersection_start, intersection_end))
        common_slots = new_common_slots
    
    # Filter out slots that conflict with any unavailable times
    filtered_slots = []
    for slot in common_slots:
        slot_start, slot_end = slot
        conflicting = False
        for person, slots in schedules.items():
            for unavail_slot in slots:
                unavail_start, unavail_end = map(to_datetime, unavail_slot)
                if not (slot_end <= unavail_start or slot_start >= unavail_end):
                    conflicting = True
                    break
            if conflicting:
                break
        if not conflicting:
            filtered_slots.append(slot)
    
    # Find a slot that fits the meeting duration
    for slot in filtered_slots:
        slot_start, slot_end = slot
        if (slot_end - slot_start) >= timedelta(minutes=meeting_duration):
            return slot_start.strftime("%H:%M"), (slot_start + timedelta(minutes=meeting_duration)).strftime("%H:%M")
    
    # If no suitable slot is found, return a message indicating so
    return None, None

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
if start_time and end_time:
    print(f"Meeting can be scheduled from {start_time} to {end_time} on {day_of_week}.")
else:
    print("No suitable meeting time found.")