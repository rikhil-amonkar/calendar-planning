from datetime import datetime, timedelta

def find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration, work_start, work_end):
    days = ['Monday', 'Tuesday']
    meeting_duration = timedelta(hours=meeting_duration)
    
    for day in days:
        jesse_busy_times = jesse_schedule.get(day, [])
        lawrence_busy_times = lawrence_schedule.get(day, [])
        
        # Convert times to datetime objects for easier manipulation
        jesse_busy_times = [(datetime.strptime(start, '%H:%M'), datetime.strptime(end, '%H:%M')) for start, end in jesse_busy_times]
        lawrence_busy_times = [(datetime.strptime(start, '%H:%M'), datetime.strptime(end, '%H:%M')) for start, end in lawrence_busy_times]
        
        # Combine and sort all busy times
        all_busy_times = sorted(jesse_busy_times + lawrence_busy_times)
        
        current_time = datetime.strptime(work_start, '%H:%M')
        end_of_day = datetime.strptime(work_end, '%H:%M')
        
        while current_time < end_of_day:
            available = True
            for start, end in all_busy_times:
                if current_time < end and current_time + meeting_duration > start:
                    current_time = end
                    available = False
                    break
            
            if available:
                return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
            
            current_time += timedelta(minutes=1)  # Increment by minute to find next possible slot

# Schedules
jesse_schedule = {
    'Monday': [('13:30', '14:00'), ('14:30', '15:00')],
    'Tuesday': [('9:00', '9:30'), ('13:00', '13:30'), ('14:00', '15:00')]
}

lawrence_schedule = {
    'Monday': [('9:00', '17:00')],
    'Tuesday': [('9:30', '10:30'), ('11:30', '12:30'), ('13:00', '13:30'), ('14:30', '15:00'), ('15:30', '16:30')]
}

# Meeting details
meeting_duration = 0.5  # in hours
work_start = '9:00'
work_end = '17:00'

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration, work_start, work_end)
print(f"Meeting Time: {meeting_time}, Day: {meeting_day}")