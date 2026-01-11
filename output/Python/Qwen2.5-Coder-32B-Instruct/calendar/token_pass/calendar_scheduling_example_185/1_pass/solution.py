def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert work hours to minutes from start of the day
    work_start_minutes = work_start * 60
    work_end_minutes = work_end * 60
    
    # Function to convert time in HH:MM format to minutes from start of the day
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    # Function to convert minutes from start of the day back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    # Create a list of busy intervals for each participant in minutes
    busy_intervals = []
    for participant in participants:
        busy_intervals.append([(time_to_minutes(start), time_to_minutes(end)) for start, end in participant['busy']])
    
    # Iterate through possible start times
    for start in range(work_start_minutes, work_end_minutes - meeting_duration + 1):
        # Check if all participants are free during the proposed meeting time
        free_for_all = True
        for intervals in busy_intervals:
            for busy_start, busy_end in intervals:
                if start < busy_end and start + meeting_duration > busy_start:
                    free_for_all = False
                    break
            if not free_for_all:
                break
        
        # Check Megan's preference to avoid meetings before 10:00
        if free_for_all and participants[1]['name'] == 'Megan' and start < time_to_minutes('10:00'):
            continue
        
        # If all checks pass, we found a suitable time
        if free_for_all:
            return f"{minutes_to_time(start)}:{minutes_to_time(start + meeting_duration)} Monday"
    
    return "No suitable time found"

# Define participants' schedules
participants = [
    {'name': 'Kimberly', 'busy': [('10:00', '10:30'), ('11:00', '12:00'), ('16:00', '16:30')]},
    {'name': 'Megan', 'busy': []},
    {'name': 'Marie', 'busy': [('10:00', '11:00'), ('11:30', '15:00'), ('16:00', '16:30')]},
    {'name': 'Diana', 'busy': [('9:30', '10:00'), ('10:30', '14:30'), ('15:30', '17:00')]}
]

# Meeting duration in minutes
meeting_duration = 30

# Work hours
work_start = 9
work_end = 17

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, work_start, work_end))