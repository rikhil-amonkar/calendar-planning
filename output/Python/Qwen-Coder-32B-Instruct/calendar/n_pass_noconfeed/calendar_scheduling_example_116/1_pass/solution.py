from datetime import datetime, timedelta

def find_meeting_time(participants, duration, preferred_start=None):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert all times to datetime objects for easier manipulation
    for person, slots in participants.items():
        participants[person] = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in slots]
    
    # Initialize available time slots as the entire workday
    available_slots = [(work_start, work_end)]
    
    # Subtract each person's busy slots from the available time slots
    for person, slots in participants.items():
        new_available_slots = []
        for start, end in available_slots:
            for busy_start, busy_end in slots:
                if busy_start < end and start < busy_end:
                    if start < busy_start:
                        new_available_slots.append((start, busy_start))
                    if busy_end < end:
                        new_available_slots.append((busy_end, end))
                else:
                    new_available_slots.append((start, end))
        available_slots = new_available_slots
    
    # Find the first slot that fits the duration and preferred start time
    for start, end in available_slots:
        if (end - start) >= timedelta(minutes=duration):
            if preferred_start and datetime.strptime(preferred_start, "%H:%M") <= start:
                return f"{start.strftime('%H:%M')}:{(start + timedelta(minutes=duration)).strftime('%H:%M')}", "Monday"
            elif not preferred_start:
                return f"{start.strftime('%H:%M')}:{(start + timedelta(minutes=duration)).strftime('%H:%M')}", "Monday"

# Participants' schedules
participants = {
    "Adam": [("14:00", "15:00")],
    "John": [("13:00", "13:30"), ("14:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Stephanie": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Anna": [("09:30", "10:00"), ("12:00", "12:30"), ("13:00", "15:30"), ("16:30", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Preferred start time for Anna
preferred_start_time = "14:30"

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, preferred_start_time)
print(f"{meeting_time}, {day_of_week}")