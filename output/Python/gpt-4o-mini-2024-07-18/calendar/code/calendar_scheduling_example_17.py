from datetime import datetime, timedelta

# Define the working hours and the meeting duration
start_hour = 9  # 9:00 AM
end_hour = 17   # 5:00 PM
meeting_duration = timedelta(minutes=30)  # 30 minutes

# Define the existing schedules
margaret_schedule = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
    (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
    (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
    (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
]

donna_schedule = [
    (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
]

helen_schedule = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
    (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
    (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
    (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
]

# Define the day of the week
day_of_week = "Monday"

def is_time_slot_available(start, end, schedule):
    for busy_start, busy_end in schedule:
        if busy_start < end and start < busy_end:
            return False
    return True

# Iterate through each half-hour time slot during working hours to find an available slot
current_time = datetime.strptime(f"{day_of_week} {start_hour:02}:00", "%A %H:%M")

while current_time + meeting_duration <= datetime.strptime(f"{day_of_week} {end_hour:02}:00", "%A %H:%M"):
    meeting_start = current_time
    meeting_end = current_time + meeting_duration
    
    if is_time_slot_available(meeting_start, meeting_end, margaret_schedule) and \
       is_time_slot_available(meeting_start, meeting_end, donna_schedule) and \
       is_time_slot_available(meeting_start, meeting_end, helen_schedule) and \
       meeting_end <= datetime.strptime(f"{day_of_week} 13:30", "%A %H:%M"):  # Helen's constraint
        print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}")
        print(day_of_week)
        break
    
    current_time += timedelta(minutes=30)  # Move to the next half-hour slot