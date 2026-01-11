def find_meeting_time(participants_busy_times, meeting_duration, work_start, work_end):
    # Convert work hours into 30-minute intervals
    work_intervals = [(hour, minute) for hour in range(work_start, work_end) for minute in [0, 30]]
    
    # Convert busy times into 30-minute intervals
    busy_intervals = []
    for busy_times in participants_busy_times.values():
        for start, end in busy_times:
            start_hour, start_minute = map(int, start.split(':'))
            end_hour, end_minute = map(int, end.split(':'))
            
            start_interval = (start_hour, start_minute)
            end_interval = (end_hour, end_minute)
            
            current_interval = start_interval
            while current_interval < end_interval:
                busy_intervals.append(current_interval)
                if current_interval[1] == 0:
                    current_interval = (current_interval[0], 30)
                else:
                    current_interval = (current_interval[0] + 1, 0)
    
    # Create a dictionary to count availability
    availability = {interval: 0 for interval in work_intervals}
    for interval in busy_intervals:
        if interval in availability:
            availability[interval] += 1
    
    # Find a time slot where everyone is free
    for i in range(len(work_intervals) - 1):
        start = work_intervals[i]
        end = work_intervals[i + 1]
        
        # Check if this slot is available for everyone
        if availability[start] == 0 and availability[end] == 0:
            start_str = f"{start[0]:02}:{start[1]:02}"
            end_str = f"{end[0]:02}:{end[1]:02}"
            return f"{start_str}:{end_str} Monday"
    
    return "No available time slot found"

# Define busy times for each participant
participants_busy_times = {
    'Patrick': [('13:30', '14:00'), ('14:30', '15:00')],
    'Shirley': [('9:00', '9:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('14:30', '15:00'), ('16:00', '17:00')],
    'Jeffrey': [('9:00', '9:30'), ('10:30', '11:00'), ('11:30', '12:00'), ('13:00', '13:30'), ('16:00', '17:00')],
    'Gloria': [('11:30', '12:00'), ('15:00', '15:30')],
    'Nathan': [('9:00', '9:30'), ('10:30', '12:00'), ('14:00', '17:00')],
    'Angela': [('9:00', '9:30'), ('10:00', '11:00'), ('12:30', '15:00'), ('15:30', '16:30')],
    'David': [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '14:00'), ('14:30', '16:30')]
}

# Meeting duration is 30 minutes
meeting_duration = 30

# Work hours are from 9:00 to 17:00
work_start = 9
work_end = 17

# Find the meeting time
meeting_time = find_meeting_time(participants_busy_times, meeting_duration, work_start, work_end)
print(meeting_time)