from datetime import datetime, timedelta

# Participant schedules
gary_schedule = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
}

david_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(hours=1)

# Function to find available time slot
def find_meeting_time(gary_schedule, david_schedule, duration):
    days = ["Monday", "Tuesday"]
    
    for day in days:
        gary_times = gary_schedule[day]
        david_times = david_schedule[day]
        
        # Combine schedules and get free slots
        blocked_times = gary_times + david_times
        blocked_times.sort(key=lambda x: x[0]) # Sort by start time
        
        start_of_day = datetime.strptime("09:00", "%H:%M")
        end_of_day = datetime.strptime("17:00", "%H:%M")
        
        # Check for free slots in between blocked times
        last_end_time = start_of_day
        
        for start, end in blocked_times:
            # If there is time between last_end_time and current start, consider it
            if last_end_time + duration <= start:
                return f"{last_end_time.strftime('%H:%M')}:{(last_end_time + duration).strftime('%H:%M')} {day}"
            # Update last_end_time to be the end of the current blocked time
            if end > last_end_time:
                last_end_time = end
                
        # Check for time after the last blocked time until end of the day
        if last_end_time + duration <= end_of_day:
            return f"{last_end_time.strftime('%H:%M')}:{(last_end_time + duration).strftime('%H:%M')} {day}"
    
    return "No available time slot found."

# Get proposed meeting time
proposed_time = find_meeting_time(gary_schedule, david_schedule, meeting_duration)
print(proposed_time)