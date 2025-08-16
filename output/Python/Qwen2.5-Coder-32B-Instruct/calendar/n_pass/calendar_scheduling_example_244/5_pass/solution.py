from datetime import datetime, timedelta

def find_meeting_time(schedules, duration, start_time, end_time, day_of_week):
    # Convert times to datetime objects for easier manipulation
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to hold available time slots
    available_slots = []

    # Define the unavailable time slots
    unavailable_slots = [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:50", "%H:%M")),
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M"))  # Updated to 11:00
    ]

    # Iterate over each minute in the workday to find common free slots
    current_time = start_time
    while current_time + timedelta(minutes=duration) <= end_time:
        # Check if current_time to current_time + duration is free for all
        if any(unavailable_start <= current_time < unavailable_end or
               unavailable_start <= current_time + timedelta(minutes=duration) <= unavailable_end or
               current_time < unavailable_start < current_time + timedelta(minutes=duration)
               for unavailable_start, unavailable_end in unavailable_slots):
            # Skip this time slot as it overlaps with the unavailable time
            current_time += timedelta(minutes=1)
            continue
        
        # Check if the current time slot is free for all participants
        if all(not (unavailable_start <= current_time < unavailable_end or
                    unavailable_start <= current_time + timedelta(minutes=duration) <= unavailable_end or
                    current_time < unavailable_start < current_time + timedelta(minutes=duration))
               for unavailable_start, unavailable_end in unavailable_slots):
            
            # Check if the current time slot is free for all participants
            if all(current_time.time() not in person_busy_times and 
                   (current_time + timedelta(minutes=duration)).time() not in person_busy_times
                   for person_busy_times in schedules.values()):
                available_slots.append((current_time.time(), (current_time + timedelta(minutes=duration)).time()))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)

    # Return the first available slot found
    if available_slots:
        start, end = available_slots[0]
        return f"{start.hour:02}:{start.minute:02}-{end.hour:02}:{end.minute:02} {day_of_week}"
    else:
        return "No available time slot found"

# Define the busy times for each participant
schedules = {
    'Walter': set(),
    'Cynthia': {datetime.strptime(time, "%H:%M").time() for time in ["09:00", "09:30", "10:00", "10:30", "13:30", "14:30", "15:00", "16:00"]},
    'Ann': {datetime.strptime(time, "%H:%M").time() for time in ["10:00", "11:00", "13:00", "13:30", "14:00", "15:00", "16:00", "16:30"]},
    'Catherine': {datetime.strptime(time, "%H:%M").time() for time in ["09:00", "11:30", "12:30", "13:30", "14:30", "17:00"]},
    'Kyle': {datetime.strptime(time, "%H:%M").time() for time in ["09:00", "09:30", "10:00", "11:30", "12:00", "12:30", "13:00", "14:30", "15:00", "16:00"]}
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
workday_start = "09:00"
workday_end = "17:00"

# Day of the week
day_of_week = "Monday"

# Find and print the meeting time
print(find_meeting_time(schedules, meeting_duration, workday_start, workday_end, day_of_week))