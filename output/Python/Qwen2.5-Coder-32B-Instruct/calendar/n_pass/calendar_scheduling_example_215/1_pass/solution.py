from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Iterate over each minute in the day from start to end
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        # Check if current time slot is available for all participants
        if all(current_time.strftime("%H:%M") not in busy_times and (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M") not in busy_times for busy_times in schedules.values()):
            available_slots.append(current_time)
        current_time += timedelta(minutes=1)
    
    # Return the earliest available slot
    if available_slots:
        start_slot = available_slots[0]
        end_slot = start_slot + timedelta(minutes=meeting_duration)
        return f"{start_slot.strftime('%H:%M')}:{end_slot.strftime('%H:%M')}", "Monday"
    else:
        return None, None

# Define the schedules of participants
schedules = {
    "Cynthia": ["09:30", "10:30", "11:30", "12:00", "13:00", "13:30", "15:00", "16:00"],
    "Lauren": ["09:00", "09:30", "10:30", "11:00", "11:30", "12:00", "13:00", "13:30", "14:00", "14:30", "15:00", "15:30", "16:00", "17:00"],
    "Robert": ["10:30", "11:00", "11:30", "12:00", "12:30", "13:30", "14:00", "16:00"]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
start_time = "09:00"
end_time = "17:00"

# Find the meeting time
meeting_time, day_of_week = find_meeting_time(schedules, meeting_duration, start_time, end_time)

# Output the result
print(f"{meeting_time}:{day_of_week}")