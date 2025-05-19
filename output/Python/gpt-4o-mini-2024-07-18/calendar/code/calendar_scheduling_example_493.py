from datetime import datetime, timedelta

# Define the participants' schedules
schedules = {
    "Tyler": [],
    "Kelly": [],
    "Stephanie": [(11, 0), (14, 30)],
    "Hannah": [],
    "Joe": [(9, 0), (10, 0), (12, 30), (14, 0)],
    "Diana": [(9, 0), (11, 30), (13, 0), (14, 30), (16, 0)],
    "Deborah": [(9, 0), (10, 30), (12, 30), (13, 30), (14, 30), (16, 0)]
}

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Create a list of all busy times
busy_times = []
for participant, blocks in schedules.items():
    for block in blocks:
        busy_start = datetime.combine(work_start.date(), time(*block))
        busy_end = busy_start + meeting_duration
        busy_times.append((busy_start, busy_end))

# Sort the busy times
busy_times.sort()

# Find the gaps in the schedule
free_slots = []
current_time = work_start

for busy_start, busy_end in busy_times:
    if current_time + meeting_duration <= busy_start:
        free_slots.append((current_time, busy_start))
    current_time = max(current_time, busy_end)

if current_time + meeting_duration <= work_end:
    free_slots.append((current_time, work_end))

# Choose the first available time slot
if free_slots:
    proposed_start, proposed_end = free_slots[0]
    proposed_time_range = f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}"
    day_of_week = proposed_start.strftime('%A')
    print(f'Time range: {{{proposed_time_range}}}, Day: {day_of_week}')
else:
    print("No available time slot found.")