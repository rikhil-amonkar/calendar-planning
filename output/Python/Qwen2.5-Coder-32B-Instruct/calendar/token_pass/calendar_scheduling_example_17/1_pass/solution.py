from datetime import datetime, timedelta

def find_meeting_time(margaret_blocked, donna_blocked, helen_blocked, meeting_duration, preferred_end_time):
    # Define the start and end of the workday
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert preferred end time to datetime object
    preferred_end_time = datetime.strptime(preferred_end_time, "%H:%M")
    
    # Generate all possible half-hour slots
    possible_slots = []
    current_slot = work_start
    while current_slot + timedelta(minutes=meeting_duration) <= work_end:
        if current_slot < preferred_end_time:
            possible_slots.append(current_slot)
        current_slot += timedelta(minutes=30)
    
    # Function to convert datetime to string in HH:MM format
    def to_hhmm(dt):
        return dt.strftime("%H:%M")
    
    # Filter slots based on each person's availability
    available_slots = set(possible_slots)
    
    for blocked in margaret_blocked:
        start, end = [datetime.strptime(t, "%H:%M") for t in blocked.split("-")]
        available_slots -= set(slot for slot in possible_slots if slot >= start and slot < end)
    
    for blocked in donna_blocked:
        start, end = [datetime.strptime(t, "%H:%M") for t in blocked.split("-")]
        available_slots -= set(slot for slot in possible_slots if slot >= start and slot < end)
    
    for blocked in helen_blocked:
        start, end = [datetime.strptime(t, "%H:%M") for t in blocked.split("-")]
        available_slots -= set(slot for slot in possible_slots if slot >= start and slot < end)
    
    # Check if there is any common slot
    if available_slots:
        # Sort the available slots to get the earliest one
        available_slots = sorted(available_slots)
        earliest_slot = available_slots[0]
        return f"{to_hhmm(earliest_slot)}:{to_hhmm(earliest_slot + timedelta(minutes=meeting_duration))} Monday"
    else:
        return "No available time slot found"

# Define the blocked times for each participant
margaret_blocked = ["09:00-10:00", "10:30-11:00", "11:30-12:00", "13:00-13:30", "15:00-15:30"]
donna_blocked = ["14:30-15:00", "16:00-16:30"]
helen_blocked = ["09:00-09:30", "10:00-11:30", "13:00-14:00", "14:30-15:00", "15:30-17:00"]

# Meeting duration in minutes
meeting_duration = 30

# Helen's preferred end time
preferred_end_time = "13:30"

# Find the meeting time
meeting_time = find_meeting_time(margaret_blocked, donna_blocked, helen_blocked, meeting_duration, preferred_end_time)
print(meeting_time)