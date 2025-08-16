def find_meeting_time(john_availability, jennifer_schedule, meeting_duration):
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_start_times = []

    for day in days:
        jennifer_busy_times = jennifer_schedule[day]
        jennifer_free_times = []
        
        # Calculate Jennifer's free times
        start_of_day = 9 * 60  # 9:00 AM in minutes
        end_of_day = 17 * 60    # 5:00 PM in minutes
        
        last_end = start_of_day
        for busy_start, busy_end in jennifer_busy_times:
            busy_start_minutes = busy_start.hour * 60 + busy_start.minute
            busy_end_minutes = busy_end.hour * 60 + busy_end.minute
            
            if last_end < busy_start_minutes:
                jennifer_free_times.append((last_end, busy_start_minutes))
            last_end = max(last_end, busy_end_minutes)
        
        if last_end < end_of_day:
            jennifer_free_times.append((last_end, end_of_day))
        
        # Check for common free time with John's preference
        for start, end in jennifer_free_times:
            if start <= 14 * 60 + 30 and end - start >= meeting_duration:
                meeting_start_times.append((start, day))
    
    # Convert the first valid time back to HH:MM format
    if meeting_start_times:
        start_minutes, day = meeting_start_times[0]
        start_hour, start_minute = divmod(start_minutes, 60)
        end_hour, end_minute = divmod(start_minutes + meeting_duration, 60)
        return f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02} {day}"
    else:
        return "No available time found"

# Define the availability and schedules
john_availability = {
    'Monday': [(9 * 60, 14 * 60 + 30)],
    'Tuesday': [(9 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 17 * 60)]
}

jennifer_schedule = {
    'Monday': [(9 * 60, 11 * 60), (11 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60 + 30), (15 * 60, 17 * 60)],
    'Tuesday': [(9 * 60, 11 * 60 + 30), (12 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

meeting_duration = 30  # 30 minutes

# Convert times to datetime.time objects for easier handling
from datetime import time

jennifer_schedule = {
    'Monday': [(time(9, 0), time(11, 0)), (time(11, 30), time(13, 0)), (time(13, 30), time(14, 30)), (time(15, 0), time(17, 0))],
    'Tuesday': [(time(9, 0), time(11, 30)), (time(12, 0), time(17, 0))],
    'Wednesday': [(time(9, 0), time(11, 30)), (time(12, 0), time(12, 30)), (time(13, 0), time(14, 0)), (time(14, 30), time(16, 0)), (time(16, 30), time(17, 0))]
}

print(find_meeting_time(john_availability, jennifer_schedule, meeting_duration))