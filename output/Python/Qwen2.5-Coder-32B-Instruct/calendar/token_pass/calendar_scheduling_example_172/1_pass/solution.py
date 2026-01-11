from datetime import datetime, timedelta

def find_meeting_time(participants_busy_times, meeting_duration, work_start, work_end, day_of_week):
    # Convert work hours to datetime objects
    work_start_dt = datetime.strptime(work_start, "%H:%M")
    work_end_dt = datetime.strptime(work_end, "%H:%M")
    
    # Create a time grid from work_start to work_end in 30 minute intervals
    current_time = work_start_dt
    time_grid = []
    while current_time < work_end_dt:
        time_grid.append(current_time)
        current_time += timedelta(minutes=30)
    
    # Initialize availability grid
    availability_grid = [True] * len(time_grid)
    
    # Mark busy times in the availability grid
    for busy_times in participants_busy_times.values():
        for start, end in busy_times:
            start_dt = datetime.strptime(start, "%H:%M")
            end_dt = datetime.strptime(end, "%H:%M")
            start_index = (start_dt - work_start_dt) // timedelta(minutes=30)
            end_index = (end_dt - work_start_dt) // timedelta(minutes=30)
            for i in range(start_index, end_index):
                availability_grid[i] = False
    
    # Find a continuous block of time that is available for all participants
    meeting_duration_slots = meeting_duration // 30  # Convert meeting duration to slots
    for i in range(len(availability_grid) - meeting_duration_slots + 1):
        if all(availability_grid[i:i+meeting_duration_slots]):
            start_time = time_grid[i].strftime("%H:%M")
            end_time = (time_grid[i] + timedelta(minutes=meeting_duration)).strftime("%H:%M")
            return f"{start_time}:{end_time} {day_of_week}"
    
    return "No available time slot found"

# Define the busy times for each participant
participants_busy_times = {
    'Patrick': [('9:00', '9:30'), ('10:00', '10:30'), ('13:30', '14:00'), ('16:00', '16:30')],
    'Kayla': [('12:30', '13:30'), ('15:00', '15:30'), ('16:00', '16:30')],
    'Carl': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '13:30'), ('14:30', '17:00')],
    'Christian': [('9:00', '12:30'), ('13:00', '14:00'), ('14:30', '17:00')]
}

# Meeting details
meeting_duration = 30  # in minutes
work_start = "09:00"
work_end = "17:00"
day_of_week = "Monday"

# Find and print the meeting time
meeting_time = find_meeting_time(participants_busy_times, meeting_duration, work_start, work_end, day_of_week)
print(meeting_time)