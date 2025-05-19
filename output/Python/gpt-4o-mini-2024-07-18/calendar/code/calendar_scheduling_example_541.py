from datetime import datetime, timedelta

# Define the participants' schedules
kayla_schedule = [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
                  
rebecca_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                    (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                    (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]

# Meeting duration
meeting_duration = timedelta(hours=1)

# Define working hours
start_of_day = datetime.strptime("09:00", "%H:%M")
end_of_day = datetime.strptime("17:00", "%H:%M")
meeting_day = "Monday"

# Create a list of all busy times
busy_times = kayla_schedule + rebecca_schedule

# Initialize free time slots
free_time_slots = []
current_time = start_of_day

# Find free time slots
for busy_start, busy_end in sorted(busy_times):
    if current_time < busy_start:
        free_time_slots.append((current_time, busy_start))
    current_time = max(current_time, busy_end)

# Account for end of day free time
if current_time < end_of_day:
    free_time_slots.append((current_time, end_of_day))

# Find a suitable time slot for the meeting
for start, end in free_time_slots:
    if end - start >= meeting_duration:
        proposed_time_start = start
        proposed_time_end = start + meeting_duration
        print(f"{proposed_time_start.strftime('%H:%M')}:{proposed_time_end.strftime('%H:%M')}")
        print(meeting_day)
        break