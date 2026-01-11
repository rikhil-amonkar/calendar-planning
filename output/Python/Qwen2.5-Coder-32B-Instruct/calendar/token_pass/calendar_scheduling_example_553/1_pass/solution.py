from datetime import datetime, timedelta

def find_meeting_time(eric_schedule, henry_schedule, meeting_duration, preferred_end_time):
    # Define the working hours
    start_of_day = datetime.strptime("09:00", "%H:%M")
    end_of_day = datetime.strptime("17:00", "%H:%M")
    
    # Convert schedules to datetime objects
    eric_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in eric_schedule]
    henry_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in henry_schedule]
    
    # Combine all busy times
    all_busy_times = eric_busy_times + henry_busy_times
    
    # Sort busy times by start time
    all_busy_times.sort()
    
    # Initialize variables to track the current time
    current_time = start_of_day
    available_slots = []
    
    # Find available slots
    for busy_start, busy_end in all_busy_times:
        if current_time < busy_start:
            available_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    
    # Check for available slots after the last busy period
    if current_time < end_of_day:
        available_slots.append((current_time, end_of_day))
    
    # Convert preferred end time to datetime object
    preferred_end_time = datetime.strptime(preferred_end_time, "%H:%M")
    
    # Find a suitable slot
    for slot_start, slot_end in available_slots:
        if (slot_end - slot_start) >= timedelta(minutes=meeting_duration) and slot_start <= preferred_end_time:
            meeting_start = slot_start
            meeting_end = meeting_start + timedelta(minutes=meeting_duration)
            return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", "Monday"
    
    # Since we know there is a solution, this line should never be reached
    return None, None

# Define the schedules and constraints
eric_schedule = [("12:00", "13:00"), ("14:00", "15:00")]
henry_schedule = [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")]
meeting_duration = 30  # in minutes
preferred_end_time = "10:00"

# Find the meeting time
meeting_time, day_of_week = find_meeting_time(eric_schedule, henry_schedule, meeting_duration, preferred_end_time)

# Output the result
print(f"Meeting time: {meeting_time} on {day_of_week}")