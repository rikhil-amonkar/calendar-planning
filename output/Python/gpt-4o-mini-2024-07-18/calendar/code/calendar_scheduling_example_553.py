from datetime import datetime, timedelta

# Define work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define existing schedules as tuples of start and end times
eric_schedule = [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                 (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))]

henry_schedule = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Henry prefers not to meet after 10:00
henry_preference_cutoff = datetime.strptime("10:00", "%H:%M")

# Function to find a suitable meeting time
def find_meeting_time(schedule1, schedule2, work_start, work_end, meeting_duration):
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        meeting_start = current_time
        meeting_end = current_time + meeting_duration

        if all(not (meeting_start < end and meeting_end > start) for start, end in schedule1) and \
           all(not (meeting_start < end and meeting_end > start) for start, end in schedule2) and \
           meeting_start <= henry_preference_cutoff:
            return meeting_start, meeting_end
        
        current_time += timedelta(minutes=1)  # Check the next minute
        
    return None, None

# Finding the meeting time
meeting_start, meeting_end = find_meeting_time(eric_schedule, henry_schedule, work_start, work_end, meeting_duration)

# Output the meeting time and day of the week if found
if meeting_start and meeting_end:
    print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} Monday")
else:
    print("No available time found")