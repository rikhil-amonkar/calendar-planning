from datetime import datetime, timedelta

def find_meeting_time(tyler_schedule, ruth_schedule, preferred_start, meeting_duration, days):
    meeting_duration = timedelta(minutes=meeting_duration)
    
    for day in days:
        tyler_busy = tyler_schedule.get(day, [])
        ruth_busy = ruth_schedule.get(day, [])
        
        # Combine and sort all busy times for the day
        all_busy_times = sorted(tyler_busy + ruth_busy, key=lambda x: x[0])
        
        current_time = datetime.strptime(f"09:00", "%H:%M")
        end_of_day = datetime.strptime("17:00", "%H:%M")
        
        while current_time < end_of_day:
            next_meeting_end = current_time + meeting_duration
            
            # Check if the current time slot is free for both
            if not any(current_time < busy_end and next_meeting_end > busy_start for busy_start, busy_end in all_busy_times):
                # Check if this time is after Tyler's preferred start time
                if current_time >= preferred_start:
                    return f"{current_time.strftime('%H:%M')}:{next_meeting_end.strftime('%H:%M')}", day
            
            # Move to the next possible start time
            if all_busy_times and current_time < all_busy_times[0][0]:
                current_time = all_busy_times[0][0]
            else:
                current_time += timedelta(minutes=15)  # Increment by 15 minutes to find the next possible slot
    
    return None, None

# Define schedules
tyler_schedule = {
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                  (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
                  (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                  (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}

ruth_schedule = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
               (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
               (datetime.strptime('12:30', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
               (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
               (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}

# Preferred start time for Tyler
preferred_start = datetime.strptime('16:00', '%H:%M')

# Meeting duration in minutes
meeting_duration = 30

# Days to consider
days = ['Monday', 'Tuesday', 'Wednesday']

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(tyler_schedule, ruth_schedule, preferred_start, meeting_duration, days)

print(f"{meeting_time}:{meeting_day}")