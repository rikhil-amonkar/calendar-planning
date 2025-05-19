from datetime import datetime, timedelta

# Define the participants' busy schedules
schedules = {
    "Jacqueline": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                   (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                   (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                   (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Harold": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Arthur": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Kelly": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Define working hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Harold prefers not to meet after 13:00
harold_preference_end = datetime.strptime("13:00", "%H:%M")

# Finding the time slot
def find_meeting_time(schedules, meeting_duration, work_start, work_end, harold_preference_end):
    # Create a list of free time slots based on the busy schedules
    free_slots = []
    current_time = work_start

    while current_time + meeting_duration <= work_end:
        is_busy = False
        for participant, busy_times in schedules.items():
            for busy_start, busy_end in busy_times:
                if busy_start <= current_time < busy_end or busy_start < current_time + meeting_duration <= busy_end:
                    is_busy = True
                    break
            if is_busy:
                break
        
        if not is_busy:
            if current_time <= harold_preference_end:
                free_slots.append(current_time)
        
        current_time += timedelta(minutes=30)

    if free_slots:
        return free_slots[0]

meeting_time = find_meeting_time(schedules, meeting_duration, work_start, work_end, harold_preference_end)
if meeting_time:
    meeting_start = meeting_time.strftime("%H:%M")
    meeting_end = (meeting_time + meeting_duration).strftime("%H:%M")
    day_of_week = "Monday"
    
    print(f"{meeting_start}:{meeting_end} {day_of_week}")