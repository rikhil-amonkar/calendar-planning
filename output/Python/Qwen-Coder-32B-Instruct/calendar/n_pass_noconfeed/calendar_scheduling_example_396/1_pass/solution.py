from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time, day_of_week):
    # Convert start_time and end_time to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to keep track of available times
    available_times = []
    
    # Iterate over each minute in the workday
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        # Check if all participants are free at this time
        is_free = True
        for person_schedule in schedules.values():
            for event_start, event_end in person_schedule:
                if current_time < event_end and current_time + timedelta(minutes=meeting_duration) > event_start:
                    is_free = False
                    break
            if not is_free:
                break
        
        # If all participants are free, add this time to the available times
        if is_free:
            available_times.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    # Return the first available time slot found
    if available_times:
        meeting_start, meeting_end = available_times[0]
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day_of_week
    else:
        return "No available time found", day_of_week

# Define the schedules for each participant
schedules = {
    'Andrea': [],
    'Jack': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
             (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    'Madison': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Rachel': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Douglas': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    'Ryan': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting parameters
meeting_duration = 30  # in minutes
start_time = "09:00"
end_time = "17:00"
day_of_week = "Monday"

# Find and print the meeting time
meeting_time, day = find_meeting_time(schedules, meeting_duration, start_time, end_time, day_of_week)
print(meeting_time, day)