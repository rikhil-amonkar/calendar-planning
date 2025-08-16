from datetime import datetime, timedelta

# Define the available days and work hours
available_days = ["Monday", "Tuesday", "Wednesday"]
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Define the blocked times for each participant
judith_blocked_times = {
    "Monday": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))]
}

timothy_blocked_times = {
    "Monday": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tuesday": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Wednesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ]
}

# Function to check if a time slot is available for both participants
def is_slot_available(day, start_time):
    end_time = start_time + meeting_duration
    
    # Check Judith's availability
    if day in judith_blocked_times:
        for blocked_start, blocked_end in judith_blocked_times[day]:
            if start_time < blocked_end and end_time > blocked_start:
                return False
    
    # Check Timothy's availability
    if day in timothy_blocked_times:
        for blocked_start, blocked_end in timothy_blocked_times[day]:
            if start_time < blocked_end and end_time > blocked_start:
                return False
    
    return True

# Find a suitable time slot
for day in available_days:
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_available(day, current_time):
            # Check Judith's preference to avoid more meetings on Monday and Wednesday before 12:00
            if day == "Monday" or (day == "Wednesday" and current_time.hour < 12):
                current_time += timedelta(minutes=30)
                continue
            
            # Output the found time slot
            print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} {day}")
            break
        
        current_time += timedelta(minutes=30)