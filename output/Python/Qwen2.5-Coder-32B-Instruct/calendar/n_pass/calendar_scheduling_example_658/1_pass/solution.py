from datetime import datetime, timedelta

# Define the work hours and constraints
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define Shirley's schedule
shirley_busy_times = {
    "Monday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M"))]
}

# Define Albert's schedule
albert_busy_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if a time slot is available for both participants
def is_slot_available(day, start_time):
    end_time = start_time + meeting_duration
    
    # Check Shirley's availability
    for busy_start, busy_end in shirley_busy_times[day]:
        if busy_start <= start_time < busy_end or busy_start < end_time <= busy_end:
            return False
    
    # Check Albert's availability
    for busy_start, busy_end in albert_busy_times[day]:
        if busy_start <= start_time < busy_end or busy_start < end_time <= busy_end:
            return False
    
    return True

# Find a suitable time slot
for day in ["Monday", "Tuesday"]:
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_available(day, current_time) and not (day == "Tuesday" and current_time >= datetime.strptime("10:30", "%H:%M")):
            start_time_str = current_time.strftime("%H:%M")
            end_time_str = (current_time + meeting_duration).strftime("%H:%M")
            print(f"{start_time_str}:{end_time_str} {day}")
            break
        current_time += timedelta(minutes=15)