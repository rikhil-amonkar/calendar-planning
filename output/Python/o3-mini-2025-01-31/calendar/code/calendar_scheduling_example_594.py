from datetime import datetime, timedelta

# Define constants
WORK_DAY = "Monday"
MEETING_DURATION = timedelta(minutes=30)
WORK_START = datetime.strptime("09:00", "%H:%M")
WORK_END = datetime.strptime("17:00", "%H:%M")

# Busy schedules for each participant (as tuples of start and end times)
# Times are provided in HH:MM format
busy_schedules = {
    "Adam": [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Roy":  [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")]
}

# Convert busy schedule times to datetime objects (relative to an arbitrary date)
def convert_schedule(schedule):
    converted = []
    for start, end in schedule:
        start_dt = datetime.strptime(start, "%H:%M")
        end_dt = datetime.strptime(end, "%H:%M")
        converted.append((start_dt, end_dt))
    return converted

# Convert busy schedules for each participant
for person in busy_schedules:
    busy_schedules[person] = convert_schedule(busy_schedules[person])

# Function to determine if a meeting time slot conflicts with any busy intervals.
def is_slot_free(meeting_start, meeting_end, schedules):
    for intervals in schedules.values():
        for busy_start, busy_end in intervals:
            # If meeting overlaps with a busy interval, return False
            if meeting_start < busy_end and busy_start < meeting_end:
                return False
    return True

# Search for the earliest available time slot
current_start = WORK_START
proposed_start = None
while current_start + MEETING_DURATION <= WORK_END:
    proposed_end = current_start + MEETING_DURATION
    if is_slot_free(current_start, proposed_end, busy_schedules):
        proposed_start = current_start
        break
    # Increment by one minute and try again
    current_start += timedelta(minutes=1)

if proposed_start:
    proposed_end = proposed_start + MEETING_DURATION
    # Format the time as HH:MM:HH:MM
    meeting_time = f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}"
    print(f"{WORK_DAY} {meeting_time}")
else:
    print("No available time slot was found.")