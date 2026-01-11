from datetime import datetime, timedelta

# Define the day and time range
day_of_week = "Monday"
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Participants' schedules
schedules = {
    "Emily": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Mason": [],
    "Maria": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Carl": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
             (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "David": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Frank": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Create a time slot dictionary
time_slots = {}
current_time = start_time
while current_time < end_time:
    time_slots[current_time] = False
    current_time += meeting_duration

# Mark busy slots
for person, schedule in schedules.items():
    for busy_start, busy_end in schedule:
        current_time = busy_start
        while current_time < busy_end:
            if current_time in time_slots:
                time_slots[current_time] = True
            current_time += meeting_duration

# Find a free slot
for start_time_slot, is_busy in time_slots.items():
    if not is_busy:
        end_time_slot = start_time_slot + meeting_duration
        if end_time_slot in time_slots and not time_slots[end_time_slot]:
            # Found a free slot
            print(f"{start_time_slot.strftime('%H:%M')}:{end_time_slot.strftime('%H:%M')} {day_of_week}")
            break