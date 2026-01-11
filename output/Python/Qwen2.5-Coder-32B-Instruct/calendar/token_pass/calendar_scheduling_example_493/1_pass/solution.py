from datetime import datetime, timedelta

def find_common_free_slot(participants, meeting_duration, work_start, work_end):
    # Convert work hours to minutes from start of the day
    work_start_minutes = (work_start.hour * 60) + work_start.minute
    work_end_minutes = (work_end.hour * 60) + work_end.minute
    
    # Initialize a list to keep track of free minutes for each participant
    free_minutes = {name: [True] * (work_end_minutes - work_start_minutes) for name in participants}
    
    # Mark busy times for each participant
    for name, busy_times in participants.items():
        for busy_start, busy_end in busy_times:
            busy_start_minutes = (busy_start.hour * 60) + busy_start.minute - work_start_minutes
            busy_end_minutes = (busy_end.hour * 60) + busy_end.minute - work_start_minutes
            for i in range(busy_start_minutes, busy_end_minutes):
                free_minutes[name][i] = False
    
    # Find a common free slot of the required duration
    for minute in range(work_end_minutes - work_start_minutes - meeting_duration + 1):
        if all(free_minutes[name][minute] for name in participants):
            start_time_minutes = minute + work_start_minutes
            start_time = work_start + timedelta(minutes=start_time_minutes)
            end_time = start_time + timedelta(minutes=meeting_duration)
            return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}"
    
    return None

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define participants and their busy times
participants = {
    "Tyler": [],
    "Kelly": [],
    "Stephanie": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Hannah": [],
    "Joe": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
            (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
            (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
            (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Diana": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Deborah": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Meeting duration in minutes
meeting_duration = 30

# Find the common free slot
common_slot = find_common_free_slot(participants, meeting_duration, work_start, work_end)

# Output the result
if common_slot:
    print(f"Meeting time: {common_slot} on Monday")
else:
    print("No common free slot found.")