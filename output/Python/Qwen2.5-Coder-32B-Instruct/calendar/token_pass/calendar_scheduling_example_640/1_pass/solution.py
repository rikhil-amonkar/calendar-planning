from datetime import datetime, timedelta

def find_meeting_time(bobby_schedule, michael_schedule, meeting_duration):
    # Convert string times to datetime objects for easier manipulation
    def parse_time(time_str):
        return datetime.strptime(time_str, "%H:%M")
    
    # Generate all possible time slots from 9:00 to 17:00 in 30-minute increments
    def generate_slots():
        start = parse_time("09:00")
        end = parse_time("17:00")
        current = start
        slots = []
        while current < end:
            slots.append((current, current + timedelta(minutes=meeting_duration)))
            current += timedelta(minutes=30)
        return slots
    
    # Check if a slot is free for a given person's schedule
    def is_slot_free(slot, person_schedule):
        for busy_slot in person_schedule:
            if not (slot[1] <= busy_slot[0] or slot[0] >= busy_slot[1]):
                return False
        return True
    
    # Find free slots for each person
    def find_free_slots(person_schedule, all_slots):
        return [slot for slot in all_slots if is_slot_free(slot, person_schedule)]
    
    # Convert busy time strings to datetime objects
    bobby_busy = [(parse_time(start), parse_time(end)) for start, end in bobby_schedule]
    michael_busy = [(parse_time(start), parse_time(end)) for start, end in michael_schedule]
    
    # Generate all possible slots
    slots = generate_slots()
    
    # Find free slots for each person
    bobby_free_slots = find_free_slots(bobby_busy, slots)
    michael_free_slots = find_free_slots(michael_busy, slots)
    
    # Find overlapping free slots
    common_free_slots = set(bobby_free_slots).intersection(set(michael_free_slots))
    
    # Find the earliest common free slot
    if common_free_slots:
        earliest_slot = min(common_free_slots, key=lambda x: x[0])
        return earliest_slot, "Monday"
    else:
        # If no slot found on Monday, check Tuesday
        # For simplicity, assume the same busy times on Tuesday
        bobby_busy_tuesday = [(t[0] + timedelta(days=1), t[1] + timedelta(days=1)) for t in bobby_busy]
        michael_busy_tuesday = [(t[0] + timedelta(days=1), t[1] + timedelta(days=1)) for t in michael_busy]
        
        bobby_free_slots_tuesday = find_free_slots(bobby_busy_tuesday, slots)
        michael_free_slots_tuesday = find_free_slots(michael_busy_tuesday, slots)
        
        common_free_slots_tuesday = set(bobby_free_slots_tuesday).intersection(set(michael_free_slots_tuesday))
        
        if common_free_slots_tuesday:
            earliest_slot_tuesday = min(common_free_slots_tuesday, key=lambda x: x[0])
            return earliest_slot_tuesday, "Tuesday"
        else:
            return None, None

# Define schedules
bobby_schedule = [("14:30", "15:00"), ("12:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")]
michael_schedule = [("9:00", "10:00"), ("10:30", "13:30"), ("14:00", "15:00"), ("15:30", "17:00"), 
                    ("12:00", "14:00"), ("15:00", "16:00"), ("16:30", "17:00")]

# Meeting duration in minutes
meeting_duration = 30

# Find meeting time
meeting_time, day = find_meeting_time(bobby_schedule, michael_schedule, meeting_duration)

# Output the result
if meeting_time:
    start_time = meeting_time[0].strftime("%H:%M")
    end_time = meeting_time[1].strftime("%H:%M")
    print(f"{start_time}:{end_time} on {day}")
else:
    print("No common free time found.")