from datetime import datetime, timedelta

# Define work hours and participants' schedules
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Existing schedules
emily_schedule = [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

melissa_schedule = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                    (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))]

frank_schedule = [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Combine all schedules
all_schedules = emily_schedule + melissa_schedule + frank_schedule

# Function to find a suitable meeting time
def find_meeting_time():
    current_time = work_start
    while current_time <= work_end - meeting_duration:
        # Check if current time conflicts with any schedule
        end_time = current_time + meeting_duration
        conflict = False
        for start, end in all_schedules:
            if (current_time < end) and (end_time > start):
                conflict = True
                break
        if not conflict:
            return current_time.strftime("%H:%M") + ":" + end_time.strftime("%H:%M"), "Monday"
        current_time += timedelta(minutes=1)

# Get the proposed time
meeting_time, day = find_meeting_time()
print(meeting_time, day)