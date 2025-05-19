from datetime import datetime, timedelta

def find_meeting_time():
    # Meeting duration
    meeting_duration = timedelta(minutes=30)

    # Participants' busy times
    daniel_busy_times = [
        (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
        (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
        (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
        (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
        (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
    ]
    
    bradley_busy_times = [
        (datetime.strptime('09:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
        (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
        (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
        (datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
    ]
    
    # Days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Check for available slots
    for day in days:
        for hour in range(9, 17):  # Working hours from 9 to 17
            start_time = datetime.strptime(f'{day} {hour}:00', '%A %H:%M')
            end_time = start_time + meeting_duration
            
            # Check if this time slot is within busy schedules
            if (end_time.hour < 17):  # Only consider time slots ending before 17:00
                is_available = True
                
                # Check Daniel's availability
                for start, end in daniel_busy_times:
                    if (start_time < end and start < end_time):
                        is_available = False
                        break
                
                if is_available:
                    # Check Bradley's availability
                    for start, end in bradley_busy_times:
                        if (start_time < end and start < end_time):
                            is_available = False
                            break
                    
                if is_available:
                    return f'{start_time.strftime("%H:%M")}:{end_time.strftime("%H:%M")}', day

# Call the function and print the output
meeting_time, meeting_day = find_meeting_time()
print(meeting_time, meeting_day)