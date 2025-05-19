import datetime

def find_meeting_time():
    # Define the working hours and meeting duration
    working_hours = (datetime.time(9, 0), datetime.time(17, 0))
    meeting_duration = datetime.timedelta(minutes=30)
    
    # Existing schedules (busy times)
    arthur_schedule = {
        'Monday': [(datetime.time(11, 0), datetime.time(11, 30)),
                   (datetime.time(13, 30), datetime.time(14, 0)),
                   (datetime.time(15, 0), datetime.time(15, 30))],
        'Tuesday': [(datetime.time(13, 0), datetime.time(13, 30)),
                    (datetime.time(16, 0), datetime.time(16, 30))],
        'Wednesday': [(datetime.time(10, 0), datetime.time(10, 30)),
                      (datetime.time(11, 0), datetime.time(11, 30)),
                      (datetime.time(12, 0), datetime.time(12, 30)),
                      (datetime.time(14, 0), datetime.time(14, 30)),
                      (datetime.time(16, 0), datetime.time(16, 30))]
    }

    michael_schedule = {
        'Monday': [(datetime.time(9, 0), datetime.time(12, 0)),
                   (datetime.time(12, 30), datetime.time(13, 0)),
                   (datetime.time(14, 0), datetime.time(14, 30)),
                   (datetime.time(15, 0), datetime.time(17, 0))],
        'Tuesday': [(datetime.time(9, 30), datetime.time(11, 30)),
                    (datetime.time(12, 0), datetime.time(13, 30)),
                    (datetime.time(14, 0), datetime.time(15, 30))],
        'Wednesday': [(datetime.time(10, 0), datetime.time(12, 30)),
                      (datetime.time(13, 0), datetime.time(13, 30))]
    }

    # Combine schedules
    schedules = {'Monday': arthur_schedule['Monday'] + michael_schedule['Monday'],
                 'Tuesday': arthur_schedule['Tuesday'] + michael_schedule['Tuesday'],
                 'Wednesday': arthur_schedule['Wednesday'] + michael_schedule['Wednesday']}
    
    # Function to check if a time slot is free
    def is_free(start, end, busy_times):
        for (busy_start, busy_end) in busy_times:
            if (start < busy_end and end > busy_start):  # Overlap check
                return False
        return True

    # Check availability for Monday, Wednesday (Tuesday is excluded for Arthur)
    days_to_check = ['Monday', 'Wednesday']

    for day in days_to_check:
        busy_times = schedules[day]
        
        # Check for available time slots in the working hours
        start_time = working_hours[0]
        while start_time + meeting_duration <= working_hours[1]:
            end_time = start_time + meeting_duration
            if is_free(start_time, end_time, busy_times):
                return f"{day} {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}"
            start_time = (datetime.datetime.combine(datetime.date.today(), start_time) + 
                           datetime.timedelta(minutes=1)).time()  # Increment by 1 minute

# Get the meeting time
meeting_time = find_meeting_time()
print(meeting_time)