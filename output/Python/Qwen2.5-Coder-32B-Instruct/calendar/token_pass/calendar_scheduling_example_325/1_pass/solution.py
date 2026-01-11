from datetime import datetime, timedelta

# Define the time range
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")

# Define participants' busy times
busy_times = {
    "Jose": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
             (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"))],
    "Keith": [(datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Logan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Megan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Gary": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
             (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
             (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
             (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Bobby": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
}

# Create a schedule representation in half-hour increments
schedule = {}
current_time = start_time
while current_time < end_time:
    schedule[current_time] = True
    current_time += timedelta(minutes=30)

# Mark unavailable slots
for person, times in busy_times.items():
    for start, end in times:
        current_time = start
        while current_time < end:
            if current_time in schedule:
                schedule[current_time] = False
            current_time += timedelta(minutes=30)

# Find available slots
meeting_duration = timedelta(minutes=30)
available_slots = []
current_time = start_time
while current_time + meeting_duration <= end_time:
    if all(schedule[current_time + timedelta(minutes=30*i)] for i in range(int(meeting_duration.total_seconds() / 1800))):
        available_slots.append(current_time)
    current_time += timedelta(minutes=30)

# Apply additional constraints (Jose's constraint)
final_slots = [slot for slot in available_slots if slot.hour * 60 + slot.minute <= 15 * 60 + 30]

# Select a suitable slot
if final_slots:
    selected_slot = final_slots[0]
    meeting_start = selected_slot.strftime("%H:%M")
    meeting_end = (selected_slot + meeting_duration).strftime("%H:%M")
    print(f"{meeting_start}:{meeting_end} Monday")
else:
    print("No suitable time found.")