from datetime import datetime, timedelta

def find_meeting_time(shirley_schedule, albert_schedule, meeting_duration, preferred_day=None):
    """
    Find a suitable time for a meeting between Shirley and Albert.
    
    Args:
    shirley_schedule (dict): Shirley's schedule for the day.
    albert_schedule (dict): Albert's schedule for the day.
    meeting_duration (int): Duration of the meeting in minutes.
    preferred_day (str, optional): Preferred day for the meeting. Defaults to None.
    
    Returns:
    tuple: A tuple containing the proposed meeting time and day.
    """
    
    # Define the start and end of the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')
    
    # Check if the meeting duration exceeds the available time slots
    if meeting_duration > (end_time - start_time).total_seconds() / 60:
        return "Meeting duration exceeds the available time slots.", None
    
    # Check if the preferred day is Monday or Tuesday
    if preferred_day == 'Monday':
        day = 'Monday'
        day_schedule = shirley_schedule.get('Monday', [])
        albert_schedule = albert_schedule.get('Monday', [])
    elif preferred_day == 'Tuesday':
        day = 'Tuesday'
        day_schedule = shirley_schedule.get('Tuesday', [])
        albert_schedule = albert_schedule.get('Tuesday', [])
    else:
        # If no preferred day is specified, try both days
        day_schedule = {}
        albert_schedule = {}
        for day in ['Monday', 'Tuesday']:
            day_schedule[day] = shirley_schedule.get(day, [])
            albert_schedule[day] = albert_schedule.get(day, [])
        
        # Try both days
        suitable_time_found = False
        for day in ['Monday', 'Tuesday']:
            day_schedule = shirley_schedule.get(day, [])
            albert_schedule = albert_schedule.get(day, [])
            
            # Find a time that works for both Shirley and Albert
            for hour in range(start_time.hour, end_time.hour):
                for minute in range(0, 60, 30):
                    time = datetime.combine(datetime.today(), datetime.min.time()).replace(hour=hour, minute=minute)
                    
                    # Check if the meeting time is within the work hours
                    if time < start_time or time > end_time:
                        continue
                    
                    # Check if the meeting time conflicts with the unavailable time slot
                    if time < datetime.strptime('09:00', '%H:%M') or time > datetime.strptime('17:00', '%H:%M'):
                        continue
                    
                    # Convert the schedule times to datetime objects
                    shirley_schedule_times = [datetime.strptime(str(t), '%H:%M') for t in day_schedule]
                    albert_schedule_times = [datetime.strptime(str(t), '%H:%M') for t in albert_schedule]
                    
                    # Check if the meeting time conflicts with Shirley's schedule
                    if time in shirley_schedule_times or time + timedelta(minutes=meeting_duration) in shirley_schedule_times:
                        continue
                    
                    # Check if the meeting time conflicts with Albert's schedule
                    if time in albert_schedule_times or time + timedelta(minutes=meeting_duration) in albert_schedule_times:
                        continue
                    
                    # If the meeting time works for both Shirley and Albert, return it
                    suitable_time_found = True
                    return f"{time.strftime('%H:%M')}-{(time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}", day
        
        # If no suitable time is found on both days, return a message
        if not suitable_time_found:
            return "No suitable time found.", None
    
    # If a suitable time is found on the preferred day, return it
    suitable_time_found = False
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, 30):
            time = datetime.combine(datetime.today(), datetime.min.time()).replace(hour=hour, minute=minute)
            
            # Check if the meeting time is within the work hours
            if time < start_time or time > end_time:
                continue
            
            # Check if the meeting time conflicts with the unavailable time slot
            if time < datetime.strptime('09:00', '%H:%M') or time > datetime.strptime('17:00', '%H:%M'):
                continue
            
            # Convert the schedule times to datetime objects
            shirley_schedule_times = [datetime.strptime(str(t), '%H:%M') for t in day_schedule]
            albert_schedule_times = [datetime.strptime(str(t), '%H:%M') for t in albert_schedule]
            
            # Check if the meeting time conflicts with Shirley's schedule
            if time in shirley_schedule_times or time + timedelta(minutes=meeting_duration) in shirley_schedule_times:
                continue
            
            # Check if the meeting time conflicts with Albert's schedule
            if time in albert_schedule_times or time + timedelta(minutes=meeting_duration) in albert_schedule_times:
                continue
            
            # If the meeting time works for both Shirley and Albert, return it
            suitable_time_found = True
            return f"{time.strftime('%H:%M')}-{(time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}", day
    
    # If no suitable time is found, return a message
    return "No suitable time found.", None

# Define the schedules
shirley_schedule = {
    'Monday': ['10:30', '12:00', '16:00'],
    'Tuesday': ['09:30']
}

albert_schedule = {
    'Monday': ['09:00', '17:00'],
    'Tuesday': ['09:30', '11:00', '11:30', '12:30', '13:00', '16:00', '16:30']
}

meeting_duration = 30  # 30 minutes

# Find a suitable time for the meeting
time, day = find_meeting_time(shirley_schedule, albert_schedule, meeting_duration, 'Monday')

# Print the result
if time is not None:
    print(f"Proposed meeting time: {time} on {day}")
else:
    print("No suitable time found.")