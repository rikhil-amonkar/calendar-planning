from datetime import datetime, timedelta

# Define the work hours and duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Participants' schedules
jeffrey_schedule = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                    (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M"))]

virginia_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                     (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                     (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                     (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

melissa_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                    (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Day of the week
day_of_week = "Monday"

# Function to check if the time slot is available
def is_time_slot_available(start_time, end_time, schedules):
    for schedule in schedules:
        if (start_time < schedule[1] and end_time > schedule[0]):
            return False
    return True

# Finding a suitable time
current_time = work_start
while current_time + meeting_duration <= work_end:
    end_time = current_time + meeting_duration
    if is_time_slot_available(current_time, end_time, jeffrey_schedule) and \
       is_time_slot_available(current_time, end_time, virginia_schedule) and \
       is_time_slot_available(current_time, end_time, melissa_schedule):
       
        # Check Melissa's preference not to meet after 14:00
        if current_time >= datetime.strptime("14:00", "%H:%M"):
            break
        
        print(f"{current_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
        print(day_of_week)
        break
    
    current_time += timedelta(minutes=30)