from datetime import datetime, timedelta

def find_meeting_time():
    # Define the workday slots (9:00 to 17:00 in 30-minute intervals)
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    current_time = start_time
    slots = []
    
    while current_time < end_time:
        slots.append(current_time.strftime("%H:%M"))
        current_time += timedelta(minutes=30)
    
    # Define busy slots for each participant
    busy_slots = {
        "Katherine": ["12:00", "12:30", "13:00", "13:30", "14:00", "14:30"],
        "Rebecca": [],
        "Julie": ["09:00", "09:30", "10:30", "11:00", "13:30", "14:00", "15:00", "15:30"],
        "Angela": ["09:00", "09:30", "10:00", "10:30", "11:00", "11:30", "12:00", "12:30", "13:00", "13:30", "14:00", "14:30", "15:00"],
        "Nicholas": ["09:30", "10:00", "10:30", "11:00", "11:30", "12:00", "12:30", "13:00", "13:30", "14:00", "14:30", "15:00", "15:30", "16:00", "16:30"],
        "Carl": ["09:00", "09:30", "10:00", "10:30", "11:00", "11:30", "12:00", "12:30", "13:00", "13:30", "14:00", "14:30", "15:00", "15:30", "16:00", "16:30"]
    }
    
    # Convert Angela's preference to avoid meetings before 15:00
    angela_avoid_before_15 = ["09:00", "09:30", "10:00", "10:30", "11:00", "11:30", "12:00", "12:30", "13:00", "13:30", "14:00", "14:30"]
    busy_slots["Angela"].extend(angela_avoid_before_15)
    busy_slots["Angela"] = list(set(busy_slots["Angela"]))  # Remove duplicates
    
    # Find a common free slot
    for i in range(len(slots) - 1):
        slot_start = slots[i]
        slot_end = slots[i + 1]
        
        if all(slot_start not in busy_slots[person] and slot_end not in busy_slots[person] for person in busy_slots):
            return f"{slot_start}:{slot_end} Monday"
    
    return "No available time slot found"

# Output the result
print(find_meeting_time())