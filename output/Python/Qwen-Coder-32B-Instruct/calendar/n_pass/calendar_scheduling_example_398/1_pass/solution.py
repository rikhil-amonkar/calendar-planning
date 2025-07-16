from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Iterate over each minute in the day to find common free slots
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        slot_start = current_time.time()
        slot_end = (current_time + timedelta(minutes=meeting_duration)).time()
        
        # Check if this slot is available for all participants
        if all(slot_start not in p and slot_end not in p for p in participants.values()):
            available_slots.append((slot_start, slot_end))
        
        current_time += timedelta(minutes=1)
    
    # Return the first available slot found
    if available_slots:
        return available_slots[0]
    else:
        return None

# Define participants' schedules as lists of tuples (start, end)
participants = {
    'Doris': [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("11:00", "%H:%M").time()),
              (datetime.strptime("13:30", "%H:%M").time(), datetime.strptime("14:00", "%H:%M").time()),
              (datetime.strptime("16:00", "%H:%M").time(), datetime.strptime("16:30", "%H:%M").time())],
    'Theresa': [(datetime.strptime("10:00", "%H:%M").time(), datetime.strptime("12:00", "%H:%M").time())],
    'Christian': [],
    'Terry': [(datetime.strptime("09:30", "%H:%M").time(), datetime.strptime("10:00", "%H:%M").time()),
              (datetime.strptime("11:30", "%H:%M").time(), datetime.strptime("12:00", "%H:%M").time()),
              (datetime.strptime("12:30", "%H:%M").time(), datetime.strptime("13:00", "%H:%M").time()),
              (datetime.strptime("13:30", "%H:%M").time(), datetime.strptime("14:00", "%H:%M").time()),
              (datetime.strptime("14:30", "%H:%M").time(), datetime.strptime("15:00", "%H:%M").time()),
              (datetime.strptime("15:30", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())],
    'Carolyn': [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("10:30", "%H:%M").time()),
                (datetime.strptime("11:00", "%H:%M").time(), datetime.strptime("11:30", "%H:%M").time()),
                (datetime.strptime("12:00", "%H:%M").time(), datetime.strptime("13:00", "%H:%M").time()),
                (datetime.strptime("13:30", "%H:%M").time(), datetime.strptime("14:30", "%H:%M").time()),
                (datetime.strptime("15:00", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())],
    'Kyle': [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("09:30", "%H:%M").time()),
             (datetime.strptime("11:30", "%H:%M").time(), datetime.strptime("12:00", "%H:%M").time()),
             (datetime.strptime("12:30", "%H:%M").time(), datetime.strptime("13:00", "%H:%M").time()),
             (datetime.strptime("14:30", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())]
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
workday_start = "09:00"
workday_end = "17:00"

# Find a suitable meeting time
meeting_time = find_meeting_time(participants, meeting_duration, workday_start, workday_end)

# Output the result
if meeting_time:
    print(f"{meeting_time[0].strftime('%H:%M')}:{meeting_time[1].strftime('%H:%M')}:Monday")
else:
    print("No available time slot found.")