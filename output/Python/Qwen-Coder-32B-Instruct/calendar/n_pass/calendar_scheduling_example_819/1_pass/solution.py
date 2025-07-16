from datetime import datetime, timedelta

def find_meeting_time(julie_schedule, ruth_schedule, meeting_duration, preferred_avoid_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_timedelta = timedelta(minutes=meeting_duration)
    
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    for day in days_of_week:
        julie_available = [(work_start, work_end)]
        ruth_available = ruth_schedule[day]
        
        # Find available slots for Ruth
        ruth_free_slots = []
        current_start = work_start
        for start, end in ruth_available:
            if current_start < start:
                ruth_free_slots.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < work_end:
            ruth_free_slots.append((current_start, work_end))
        
        # Find common slots between Julie and Ruth
        for j_start, j_end in julie_available:
            for r_start, r_end in ruth_free_slots:
                common_start = max(j_start, r_start)
                common_end = min(j_end, r_end)
                if common_end - common_start >= meeting_timedelta:
                    # Check if the slot is preferred
                    if not (day == "Thursday" and common_start.time() < preferred_avoid_time):
                        return f"{common_start.strftime('%H:%M')}:{(common_start + meeting_timedelta).strftime('%H:%M')}", day
    return None

# Define the schedules
julie_schedule = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": []
}

ruth_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Meeting details
meeting_duration = 30  # in minutes
preferred_avoid_time = datetime.strptime("11:30", "%H:%M").time()

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(julie_schedule, ruth_schedule, meeting_duration, preferred_avoid_time)
print(f"{meeting_time}, {meeting_day}")