from datetime import datetime, timedelta

# Define the working hours and participants' schedules
working_hours_start = datetime.strptime("09:00", "%H:%M")
working_hours_end = datetime.strptime("17:00", "%H:%M")

# Existing schedules (start, end)
julie_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

sean_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                 (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

lori_schedule = [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                 (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Duration of the meeting
meeting_duration = timedelta(hours=1)

# Function to find a suitable meeting time
def find_meeting_time():
    current_time = working_hours_start
    
    while current_time + meeting_duration <= working_hours_end:
        next_time = current_time + meeting_duration
        if is_time_available(current_time, next_time):
            return current_time.strftime("%H:%M") + ":" + next_time.strftime("%H:%M")
        current_time += timedelta(minutes=1)
    
    return None

def is_time_available(start_time, end_time):
    for busy_period in julie_schedule + sean_schedule + lori_schedule:
        if (start_time < busy_period[1]) and (end_time > busy_period[0]):
            return False
    return True

# Execute the function to get proposed meeting time
proposed_time = find_meeting_time()

# Output the proposed time along with the day of the week
day_of_week = "Monday"
if proposed_time:
    print(f"{proposed_time} {day_of_week}")