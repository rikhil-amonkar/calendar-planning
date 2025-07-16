from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to store available slots
    available_slots = []
    
    # Iterate over each minute in the workday
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        # Check if all participants are free at this time
        free_for_all = True
        for person, busy_times in schedules.items():
            for busy_start, busy_end in busy_times:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    free_for_all = False
                    break
            if not free_for_all:
                break
        
        # If all participants are free, add this slot to available slots
        if free_for_all:
            available_slots.append((current_time.strftime("%H:%M"), (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    # Return the first available slot
    return available_slots[0] if available_slots else None

# Define the schedules for each participant
schedules = {
    "Andrea": [("09:30", "10:30"), ("13:30", "14:30")],
    "Ruth": [("12:30", "13:00"), ("15:00", "15:30")],
    "Steven": [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("15:00", "16:00")],
    "Grace": [],
    "Kyle": [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Elijah": [("09:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Lori": [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
start_time = "09:00"
end_time = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, start_time, end_time)

# Output the result
if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]}, Monday")
else:
    print("No available time found.")