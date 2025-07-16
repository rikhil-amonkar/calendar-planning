from datetime import datetime, timedelta

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the available days
available_days = ['Monday', 'Tuesday', 'Wednesday']

# Define the busy times for each participant
nicole_busy_times = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
               (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
               (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                (datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M'))],
    'Wednesday': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                  (datetime.strptime('12:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                  (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}

ruth_busy_times = {
    'Monday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Tuesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Wednesday': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                  (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                  (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
                  (datetime.strptime('13:30', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
                  (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]
}

# Function to check if a time slot is free for both participants
def is_slot_free(day, start_time):
    end_time = start_time + meeting_duration
    
    # Check Nicole's availability
    for busy_start, busy_end in nicole_busy_times[day]:
        if busy_start <= start_time < busy_end or busy_start < end_time <= busy_end:
            return False
    
    # Check Ruth's availability
    for busy_start, busy_end in ruth_busy_times[day]:
        if busy_start <= start_time < busy_end or busy_start < end_time <= busy_end:
            return False
    
    return True

# Find a suitable time slot
for day in available_days:
    start_time = datetime.strptime('09:00', '%H:%M')
    while start_time + meeting_duration <= datetime.strptime('17:00', '%H:%M'):
        if is_slot_free(day, start_time):
            print(f"{start_time.strftime('%H:%M')}:{(start_time + meeting_duration).strftime('%H:%M')} {day}")
            break
        start_time += timedelta(minutes=15)