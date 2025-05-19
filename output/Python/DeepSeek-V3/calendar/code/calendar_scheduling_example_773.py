def find_earliest_meeting_time(participant_busy_times, work_hours, meeting_duration, days):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = int(work_hours[0].split(':')[0]) * 60 + int(work_hours[0].split(':')[1])
    work_end = int(work_hours[1].split(':')[0]) * 60 + int(work_hours[1].split(':')[1])
    
    for day in days:
        # Get busy slots for the current day
        busy_slots = participant_busy_times.get(day, [])
        
        # Convert busy slots to minutes since midnight and sort them
        busy_minutes = []
        for slot in busy_slots:
            start = slot[0].split(':')
            end = slot[1].split(':')
            start_min = int(start[0]) * 60 + int(start[1])
            end_min = int(end[0]) * 60 + int(end[1])
            busy_minutes.append((start_min, end_min))
        
        # Sort busy slots by start time
        busy_minutes.sort()
        
        # Check the time before the first busy slot
        if len(busy_minutes) > 0:
            first_busy_start = busy_minutes[0][0]
            available_start = work_start
            available_end = first_busy_start
            if available_end - available_start >= meeting_duration:
                return day, (available_start, available_start + meeting_duration)
        
        # Check the time between busy slots
        for i in range(len(busy_minutes) - 1):
            current_end = busy_minutes[i][1]
            next_start = busy_minutes[i + 1][0]
            if next_start - current_end >= meeting_duration:
                return day, (current_end, current_end + meeting_duration)
        
        # Check the time after the last busy slot
        if len(busy_minutes) > 0:
            last_busy_end = busy_minutes[-1][1]
            available_start = last_busy_end
            available_end = work_end
            if available_end - available_start >= meeting_duration:
                return day, (available_start, available_start + meeting_duration)
        else:
            # No busy slots, the entire work day is available
            return day, (work_start, work_start + meeting_duration)
    
    return None, None

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define the problem constraints
work_hours = ('9:00', '17:00')
meeting_duration = 60  # minutes
days = ['Monday', 'Tuesday', 'Wednesday']

# Roy's busy times (Patrick is free all the time)
roy_busy_times = {
    'Monday': [('10:00', '11:30'), ('12:00', '13:00'), ('14:00', '14:30'), ('15:00', '17:00')],
    'Tuesday': [('10:30', '11:30'), ('12:00', '14:30'), ('15:00', '15:30'), ('16:00', '17:00')],
    'Wednesday': [('9:30', '11:30'), ('12:30', '14:00'), ('14:30', '15:30'), ('16:30', '17:00')]
}

# Find the earliest meeting time
day, (start_min, end_min) = find_earliest_meeting_time(roy_busy_times, work_hours, meeting_duration, days)

# Format the output
start_time = format_time(start_min)
end_time = format_time(end_min)
print(f"{day}:{start_time}:{end_time}")