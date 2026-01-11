from datetime import datetime, timedelta

# Helper function to convert string time to datetime object
def time_to_datetime(time_str):
    return datetime.strptime(time_str, '%H:%M')

# Helper function to check if two time intervals overlap
def intervals_overlap(interval1, interval2):
    return interval1[0] < interval2[1] and interval2[0] < interval1[1]

# Helper function to find free intervals in a day
def find_free_intervals(busy_times, day_start='09:00', day_end='17:00'):
    day_start_dt = time_to_datetime(day_start)
    day_end_dt = time_to_datetime(day_end)
    
    # Sort busy times by start time
    busy_times.sort()
    
    free_intervals = []
    current_time = day_start_dt
    
    for busy_start, busy_end in busy_times:
        busy_start_dt = time_to_datetime(busy_start)
        busy_end_dt = time_to_datetime(busy_end)
        
        if current_time < busy_start_dt:
            free_intervals.append((current_time.time().strftime('%H:%M'), busy_start_dt.time().strftime('%H:%M')))
        
        current_time = max(current_time, busy_end_dt)
    
    if current_time < day_end_dt:
        free_intervals.append((current_time.time().strftime('%H:%M'), day_end_dt.time().strftime('%H:%M')))
    
    return free_intervals

# Function to find a suitable meeting time
def find_meeting_time(stephanie_schedule, betty_schedule, meeting_duration=60, preferred_days=['Monday', 'Tuesday', 'Wednesday']):
    days_of_week = ['Monday', 'Tuesday', 'Wednesday']
    
    for day in days_of_week:
        if day == 'Monday':
            # Stephanie avoids Monday
            continue
        
        stephanie_busy_times = stephanie_schedule.get(day, [])
        betty_busy_times = betty_schedule.get(day, [])
        
        if day == 'Tuesday':
            # Betty cannot meet on Tuesday after 12:30
            betty_busy_times.append(('12:30', '17:00'))
        
        stephanie_free_intervals = find_free_intervals(stephanie_busy_times)
        betty_free_intervals = find_free_intervals(betty_busy_times)
        
        for stephanie_interval in stephanie_free_intervals:
            for betty_interval in betty_free_intervals:
                if intervals_overlap(stephanie_interval, betty_interval):
                    # Calculate the overlap
                    overlap_start = max(time_to_datetime(stephanie_interval[0]), time_to_datetime(betty_interval[0]))
                    overlap_end = min(time_to_datetime(stephanie_interval[1]), time_to_datetime(betty_interval[1]))
                    
                    if (overlap_end - overlap_start).seconds >= meeting_duration * 60:
                        return f"{overlap_start.strftime('%H:%M')}:{overlap_end.strftime('%H:%M')}", day
    
    return None, None

# Stephanie and Betty's schedules
stephanie_schedule = {
    'Monday': [('09:30', '10:00'), ('10:30', '11:00'), ('11:30', '12:00'), ('14:00', '14:30')],
    'Tuesday': [('12:00', '13:00')],
    'Wednesday': [('09:00', '10:00'), ('13:00', '14:00')]
}

betty_schedule = {
    'Monday': [('09:00', '10:00'), ('11:00', '11:30'), ('14:30', '15:00'), ('15:30', '16:00')],
    'Tuesday': [('09:00', '09:30'), ('11:30', '12:00'), ('12:30', '14:30'), ('15:30', '16:00')],
    'Wednesday': [('10:00', '11:30'), ('12:00', '14:00'), ('14:30', '17:00')]
}

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(stephanie_schedule, betty_schedule)

if meeting_time:
    print(f"Meeting Time: {meeting_time}, Day: {meeting_day}")
else:
    print("No suitable meeting time found.")