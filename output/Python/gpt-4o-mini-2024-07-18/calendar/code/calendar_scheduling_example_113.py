import datetime

# Define participant schedules
schedules = {
    'Bradley': [(datetime.time(9, 30), datetime.time(10, 0)),
                (datetime.time(12, 30), datetime.time(13, 0)),
                (datetime.time(13, 30), datetime.time(14, 0)),
                (datetime.time(15, 30), datetime.time(16, 0))],
    'Teresa': [(datetime.time(10, 30), datetime.time(11, 0)),
               (datetime.time(12, 0), datetime.time(12, 30)),
               (datetime.time(13, 0), datetime.time(13, 30)),
               (datetime.time(14, 30), datetime.time(15, 0))],
    'Elizabeth': [(datetime.time(9, 0), datetime.time(9, 30)),
                  (datetime.time(10, 30), datetime.time(11, 30)),
                  (datetime.time(13, 0), datetime.time(13, 30)),
                  (datetime.time(14, 30), datetime.time(15, 0)),
                  (datetime.time(15, 30), datetime.time(17, 0))],
    'Christian': [(datetime.time(9, 0), datetime.time(9, 30)),
                  (datetime.time(10, 30), datetime.time(17, 0))]
}

# Define the meeting duration
meeting_duration = datetime.timedelta(minutes=30)

# Define work hours
work_start = datetime.time(9, 0)
work_end = datetime.time(17, 0)

# Find available time slots
def find_meeting_time(schedules, duration):
    # Create a full day schedule based on work hours
    all_meeting_times = []

    current_time = datetime.datetime.combine(datetime.date.today(), work_start)
    end_of_day = datetime.datetime.combine(datetime.date.today(), work_end)

    while current_time + duration <= end_of_day:
        temp_time = current_time.time()
        is_available = True
        
        for busy_times in schedules.values():
            for start, end in busy_times:
                if start <= temp_time < end or start < (current_time + duration).time() <= end:
                    is_available = False
                    break
            if not is_available:
                break
        
        if is_available:
            all_meeting_times.append((temp_time, (current_time + duration).time()))
        
        current_time += datetime.timedelta(minutes=30)  # Increment by 30 minutes
    
    return all_meeting_times

# Get available slots
available_slots = find_meeting_time(schedules, meeting_duration)

# Assume first available slot is chosen
if available_slots:
    chosen_time = available_slots[0]
    print(f'{{{chosen_time[0].strftime("%H:%M")}:{chosen_time[1].strftime("%H:%M")}}}')
    print('Monday')