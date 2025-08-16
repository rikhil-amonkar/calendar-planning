from datetime import datetime, timedelta

def find_meeting_time(schedules, duration, start_time, end_time):
    # Convert start_time and end_time to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to hold available time slots
    available_slots = []
    
    # Iterate over each minute in the day from start to end
    current_time = start
    while current_time + timedelta(minutes=duration) <= end:
        # Check if the current time slot is free for all participants
        is_free = True
        for person_schedule in schedules.values():
            for busy_start, busy_end in person_schedule:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=duration) <= busy_end_dt:
                    is_free = False
                    break
            if not is_free:
                break
        
        # If the slot is free for everyone, add it to available_slots
        if is_free:
            available_slots.append((current_time.strftime("%H:%M"), (current_time + timedelta(minutes=duration)).strftime("%H:%M")))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    # Return the first available slot
    return available_slots[0] if available_slots else None

# Define the schedules for each participant
schedules = {
    "Doris": [("9:00", "11:00"), ("13:30", "14:00"), ("16:00", "16:30")],
    "Theresa": [("10:00", "12:00")],
    "Christian": [],
    "Terry": [("9:30", "10:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Carolyn": [("9:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"), ("13:30", "14:30"), ("15:00", "17:00")],
    "Kyle": [("9:00", "9:30"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:30", "17:00")]
}

# Define the meeting duration and time range
meeting_duration = 30  # in minutes
day_start_time = "9:00"
day_end_time = "17:00"

# Find a suitable meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, day_start_time, day_end_time)

# Output the result
if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]} Monday")
else:
    print("No available time slot found.")