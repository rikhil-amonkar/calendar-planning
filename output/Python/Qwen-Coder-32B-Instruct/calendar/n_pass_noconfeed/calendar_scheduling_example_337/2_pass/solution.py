from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert work hours to datetime objects
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    
    # Initialize available time slots for all participants
    available_slots = {work_start + timedelta(minutes=i) for i in range(0, int((work_end - work_start).total_seconds() / 60))}
    
    # Remove unavailable slots based on participants' schedules
    for person, slots in participants.items():
        for slot in slots:
            start, end = slot.split(" to ")
            start = datetime.strptime(start, "%H:%M")
            end = datetime.strptime(end, "%H:%M")
            unavailable_slots = {start + timedelta(minutes=i) for i in range(0, int((end - start).total_seconds() / 60))}
            available_slots -= unavailable_slots
    
    # Find continuous available slots that match the meeting duration
    meeting_duration = timedelta(minutes=meeting_duration)
    available_slots = sorted(list(available_slots))
    for i in range(len(available_slots) - meeting_duration.seconds // 60 + 1):
        start_time = available_slots[i]
        end_time = start_time + meeting_duration
        if all(slot in available_slots for slot in [start_time + timedelta(minutes=j) for j in range(meeting_duration.seconds // 60)]):
            return f"{start_time.strftime('%H:%M')}-{end_time.strftime('%H:%M')}", "Monday"
    
    return None, None

# Participants' schedules
participants = {
    "John": ["11:30 to 12:00", "14:00 to 14:30"],
    "Megan": ["12:00 to 12:30", "14:00 to 15:00", "15:30 to 16:00"],
    "Brandon": [],
    "Kimberly": ["9:00 to 9:30", "10:00 to 10:30", "11:00 to 14:30", "15:00 to 16:00", "16:30 to 17:00"],
    "Sean": ["10:00 to 11:00", "11:30 to 14:00", "15:00 to 15:30"],
    "Lori": ["9:00 to 9:30", "10:30 to 12:00", "13:00 to 14:30", "16:00 to 16:30"]
}

# Meeting details
meeting_duration = 30  # in minutes
work_start = "09:00"
work_end = "17:00"

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, work_start, work_end)
print(f"{meeting_time}, {day_of_week}")