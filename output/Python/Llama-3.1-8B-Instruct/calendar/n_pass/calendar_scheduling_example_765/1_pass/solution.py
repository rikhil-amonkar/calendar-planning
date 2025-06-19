from datetime import datetime, timedelta

def find_meeting_time(joshua_schedule, joyce_schedule, meeting_duration, preferred_days):
    # Find available time slots for Joshua and Joyce
    joshua_available = []
    joyce_available = []
    
    for day, schedule in joshua_schedule.items():
        for start, end in schedule:
            joshua_available.append((start, end, day))
            
    for day, schedule in joyce_schedule.items():
        for start, end in schedule:
            joyce_available.append((start, end, day))
            
    # Filter available time slots based on preferred days
    available_days = [day for day in joshua_schedule.keys() if day in preferred_days]
    
    joshua_available = [slot for slot in joshua_available if slot[2] in available_days]
    joyce_available = [slot for slot in joyce_available if slot[2] in available_days]
    
    # Find overlapping time slots
    overlapping_slots = []
    for joshua_slot in joshua_available:
        for joyce_slot in joyce_available:
            if (joshua_slot[0] >= joyce_slot[0] and joshua_slot[0] < joyce_slot[1] and 
                joyce_slot[0] >= joshua_slot[0] and joyce_slot[0] < joshua_slot[1]):
                overlapping_slots.append((max(joshua_slot[0], joyce_slot[0]), 
                                          min(joshua_slot[1], joyce_slot[1]), 
                                          joshua_slot[2]))
    
    # Find time slots that are long enough for the meeting
    long_enough_slots = []
    for slot in overlapping_slots:
        if slot[1] - slot[0] >= meeting_duration:
            long_enough_slots.append(slot)
    
    # Sort time slots by start time
    long_enough_slots.sort(key=lambda x: x[0])
    
    # Find the first available time slot that is long enough
    for slot in long_enough_slots:
        if slot[1] - slot[0] >= meeting_duration:
            return f"{slot[2]} - {slot[0]:02d}:{slot[0].minute:02d} to {slot[1]:02d}:{slot[1].minute:02d}"
    
    return "No available time slot found"

# Define schedules
joshua_schedule = {
    "Monday": [(9, 17), (15, 30)],
    "Tuesday": [(11, 30), (13, 0), (14, 30, 15)],
    "Wednesday": [(9, 17)]
}

joyce_schedule = {
    "Monday": [(9, 30), (10, 0), (11, 0, 12, 30), (13, 0, 15, 0), (15, 30, 17, 0)],
    "Tuesday": [(9, 0, 17, 0)],
    "Wednesday": [(9, 30), (10, 0), (12, 30, 15, 30), (16, 0, 16, 30)]
}

# Define meeting duration and preferred days
meeting_duration = timedelta(hours=0, minutes=30)
preferred_days = ["Monday", "Tuesday", "Wednesday"]

# Find meeting time
print(find_meeting_time(joshua_schedule, joyce_schedule, meeting_duration, preferred_days))