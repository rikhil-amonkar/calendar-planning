def find_meeting_time(schedules, meeting_duration=30, work_start=9*60, work_end=17*60):
    # Convert work hours to minutes from start of the day for easier calculations
    work_start_minutes = work_start
    work_end_minutes = work_end
    
    # Create a list of all 30-minute slots in the workday
    slots = [(start, start + meeting_duration) for start in range(work_start_minutes, work_end_minutes, meeting_duration)]
    
    # Mark all slots as available
    availability = [True] * len(slots)
    
    # Function to convert time in minutes to HH:MM format
    def minutes_to_hhmm(minutes):
        return f"{minutes // 60:02}:{minutes % 60:02}"
    
    # Mark slots as unavailable based on each person's schedule
    for person_schedule in schedules.values():
        for start, end in person_schedule:
            start_minutes = start[0] * 60 + start[1]
            end_minutes = end[0] * 60 + end[1]
            
            for i, (slot_start, slot_end) in enumerate(slots):
                if not (slot_end <= start_minutes or slot_start >= end_minutes):
                    availability[i] = False
    
    # Find the first available slot
    for i, available in enumerate(availability):
        if available:
            start_slot, end_slot = slots[i]
            return f"{minutes_to_hhmm(start_slot)}:{minutes_to_hhmm(end_slot)} Monday"
    
    return "No available time found"

# Define the schedules in the format (hour, minute)
schedules = {
    'John': [((11, 30), (12, 0)), ((14, 0), (14, 30))],
    'Megan': [((12, 0), (12, 30)), ((14, 0), (15, 0)), ((15, 30), (16, 0))],
    'Brandon': [],
    'Kimberly': [((9, 0), (9, 30)), ((10, 0), (10, 30)), ((11, 0), (14, 30)), ((15, 0), (16, 0)), ((16, 30), (17, 0))],
    'Sean': [((10, 0), (11, 0)), ((11, 30), (14, 0)), ((15, 0), (15, 30))],
    'Lori': [((9, 0), (9, 30)), ((10, 30), (12, 0)), ((13, 0), (14, 30)), ((16, 0), (16, 30))]
}

# Find and print the meeting time
meeting_time = find_meeting_time(schedules)
print(meeting_time)