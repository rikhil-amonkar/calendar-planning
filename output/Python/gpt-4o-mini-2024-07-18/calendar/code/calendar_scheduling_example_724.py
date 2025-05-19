from datetime import datetime, timedelta

# Define the meeting duration and participants' work hours
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
days = ['Monday', 'Tuesday', 'Wednesday']

# Define participants' schedules
tyler_schedule = {
    'Tuesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    'Wednesday': [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

ruth_schedule = {
    'Monday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Tuesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Wednesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if time slot is available
def is_time_available(schedule, start_time, end_time):
    for busy_start, busy_end in schedule:
        if (start_time < busy_end and end_time > busy_start):
            return False
    return True

# Main logic to find a suitable time for the meeting
def find_meeting_time():
    for day in days:
        if day in tyler_schedule or day in ruth_schedule:
            day_start = work_start
            while day_start + meeting_duration <= work_end:
                day_end = day_start + meeting_duration
                
                tyler_available = True
                ruth_available = True
                
                if day in tyler_schedule:
                    tyler_available = is_time_available(tyler_schedule[day], day_start, day_end)
                if day in ruth_schedule:
                    ruth_available = is_time_available(ruth_schedule[day], day_start, day_end)
                
                # Check if both are available at this time
                if tyler_available and ruth_available:
                    return f"{day_start.strftime('%H:%M')}:{day_end.strftime('%H:%M')}:{day}"
                
                day_start += timedelta(minutes=10)  # Check next slot

# Output the result
meeting_time = find_meeting_time()
print(meeting_time)