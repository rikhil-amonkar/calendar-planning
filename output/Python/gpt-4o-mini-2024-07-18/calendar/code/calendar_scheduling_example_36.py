from datetime import datetime, timedelta

def find_meeting_time():
    # Define work hours and meeting duration
    start_work_hour = datetime.strptime("09:00", "%H:%M")
    end_work_hour = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(hours=1)
    
    # Define existing schedules
    ryan_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                     (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"))]
    
    ruth_schedule = []  # No meetings
    
    denise_schedule = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                       (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                       (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

    # Define the available time slots
    available_slots = []
    
    current_time = start_work_hour
    
    while current_time + meeting_duration <= end_work_hour:
        next_time = current_time + meeting_duration
        
        # Check if the current time slot is busy for any participant
        is_busy = False
        for busy_start, busy_end in ryan_schedule + denise_schedule:
            if busy_start <= current_time < busy_end or busy_start < next_time <= busy_end:
                is_busy = True
                break
                
        if not is_busy:
            available_slots.append((current_time, next_time))
        
        current_time += timedelta(minutes=30)  # Check every 30 minutes
        
    # Select the first available time slot
    if available_slots:
        meeting_start, meeting_end = available_slots[0]
        meeting_time_str = f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}"
        day_of_week = "Monday"  # Given in the task
        print(f"{meeting_time_str} {day_of_week}")

find_meeting_time()