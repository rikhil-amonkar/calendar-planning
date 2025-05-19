from datetime import datetime, time, timedelta

# Define work hours and meeting duration
work_start = time(9, 0)
work_end = time(17, 0)
meeting_duration = timedelta(minutes=30)

# Define existing schedules
mary_schedule = {
    'Tuesday': [(time(10, 0), time(10, 30)), (time(15, 30), time(16, 0))],
    'Wednesday': [(time(9, 30), time(10, 0)), (time(15, 0), time(15, 30))],
    'Thursday': [(time(9, 0), time(10, 0)), (time(10, 30), time(11, 30))],
}

alexis_schedule = {
    'Monday': [(time(9, 0), time(10, 0)), (time(10, 30), time(12, 0)), (time(12, 30), time(16, 30))],
    'Tuesday': [(time(9, 0), time(10, 0)), (time(10, 30), time(11, 30)), (time(12, 0), time(15, 30)), (time(16, 0), time(17, 0))],
    'Wednesday': [(time(9, 0), time(11, 0)), (time(11, 30), time(17, 0))],
    'Thursday': [(time(10, 0), time(12, 0)), (time(14, 0), time(14, 30)), (time(15, 30), time(16, 0)), (time(16, 30), time(17, 0))],
}

# Function to find time slot for meeting
def find_meeting_time(mary_schedule, alexis_schedule, meeting_duration):
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    for day in days:
        mary_busy_times = mary_schedule.get(day, [])
        alexis_busy_times = alexis_schedule.get(day, [])
        
        # All busy times combined
        busy_times = mary_busy_times + alexis_busy_times
        
        # Sorting busy times
        busy_times.sort()
        
        # Find available time slots
        last_end_time = work_start
        for start, end in busy_times:
            if last_end_time + meeting_duration <= start:
                return f'{last_end_time.strftime("%H:%M")}:{(last_end_time + meeting_duration).strftime("%H:%M")} {day}'
            last_end_time = max(last_end_time, end)
        
        # Check after last busy time until end of work hours
        if last_end_time + meeting_duration <= work_end:
            return f'{last_end_time.strftime("%H:%M")}:{(last_end_time + meeting_duration).strftime("%H:%M")} {day}'

# Get the proposed meeting time
proposed_time = find_meeting_time(mary_schedule, alexis_schedule, meeting_duration)
print(proposed_time)