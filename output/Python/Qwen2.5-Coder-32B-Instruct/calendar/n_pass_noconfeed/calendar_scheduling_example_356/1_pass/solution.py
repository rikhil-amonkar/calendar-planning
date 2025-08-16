from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferred_start, preferred_end):
    # Convert times to datetime objects for easier manipulation
    start_time = datetime.strptime(preferred_start, "%H:%M")
    end_time = datetime.strptime(preferred_end, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    current_time = start_time
    
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    # Check each slot against all participants' schedules
    for slot_start, slot_end in available_slots:
        available_for_all = True
        for person, schedule in participants.items():
            for busy_start, busy_end in schedule:
                if slot_start < busy_end and slot_end > busy_start:
                    available_for_all = False
                    break
            if not available_for_all:
                break
        
        if available_for_all:
            return slot_start.strftime("%H:%M"), slot_end.strftime("%H:%M")
    
    return None, None

# Participants' schedules
participants = {
    "Katherine": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Rebecca": [],
    "Julie": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
              (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Angela": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Nicholas": [(datetime.strptime("9:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                 (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Carl": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
             (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
             (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
             (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

meeting_duration = 30  # Meeting duration in minutes
preferred_start = "9:00"
preferred_end = "17:00"

start, end = find_meeting_time(participants, meeting_duration, preferred_start, preferred_end)

if start and end:
    print(f"{start}:{end} Monday")
else:
    print("No available time found.")