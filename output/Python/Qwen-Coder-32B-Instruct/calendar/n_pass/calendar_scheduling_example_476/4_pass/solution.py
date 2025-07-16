from datetime import datetime, timedelta

def find_meeting_time(participants, duration, preferred_start):
    day_of_week = "Monday"
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    
    # Convert preferred start time to datetime object
    preferred_start_time = datetime.strptime(preferred_start, "%H:%M")
    
    # Initialize availability dictionary
    availability = {name: [] for name in participants}
    
    # Populate availability dictionary with free slots
    for name, schedule in participants.items():
        current_time = start_time
        for event in sorted(schedule):
            if current_time < event[0]:
                availability[name].append((current_time, event[0]))
            current_time = max(current_time, event[1])
        if current_time < end_time:
            availability[name].append((current_time, end_time))
    
    # Find common free slot
    common_free_slots = []
    participant_names = list(participants.keys())  # Convert dict_keys to list
    
    # Use a set to keep track of common free slots
    common_free_slots_set = set(availability[participant_names[0]])
    
    for name in participant_names[1:]:
        personal_slots = set(availability[name])
        common_free_slots_set = common_free_slots_set.intersection(personal_slots)
    
    # Convert the set back to a list of tuples
    common_free_slots = list(common_free_slots_set)
    
    # Sort the common free slots by start time
    common_free_slots.sort(key=lambda x: x[0])
    
    # Find the first slot that fits the duration and preferred start time
    meeting_start = None
    meeting_end = None
    for slot in common_free_slots:
        if slot[1] - slot[0] >= timedelta(minutes=duration) and slot[0] >= preferred_start_time:
            meeting_start = slot[0]
            meeting_end = meeting_start + timedelta(minutes=duration)
            break
    
    # Format the output
    if meeting_start is not None and meeting_end is not None:
        meeting_start_str = meeting_start.strftime("%H:%M")
        meeting_end_str = meeting_end.strftime("%H:%M")
        print(f"Meeting scheduled from {meeting_start_str} to {meeting_end_str} on {day_of_week}")
    else:
        print("No suitable meeting time found.")

# Define participants' schedules
participants = {
    "Daniel": [],
    "Kathleen": [(datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Carolyn": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))],
    "Roger": [],
    "Cheryl": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Virginia": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                 (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Angela": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Meeting duration in minutes
meeting_duration = 30

# Preferred start time
preferred_start_time = "12:30"

# Find and print the meeting time
find_meeting_time(participants, meeting_duration, preferred_start_time)