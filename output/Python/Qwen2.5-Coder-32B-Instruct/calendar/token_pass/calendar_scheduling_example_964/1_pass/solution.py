def parse_busy_times(busy_str):
    """Parse a string of busy times into a list of tuples (start, end)."""
    busy_times = []
    for entry in busy_str.split(', '):
        start, end = entry.split(' to ')
        busy_times.append((int(start[:2]), int(end[:2])))
    return busy_times

def is_slot_available(slot_start, slot_end, busy_times):
    """Check if a given slot is available given the busy times."""
    for busy_start, busy_end in busy_times:
        if slot_start < busy_end and slot_end > busy_start:
            return False
    return True

def find_meeting_time(betty_busy, megan_busy, meeting_duration=1, work_start=9, work_end=17):
    """Find a suitable meeting time for Betty and Megan."""
    days = {
        'Monday': betty_busy['Monday'],
        'Tuesday': betty_busy['Tuesday'],
        'Friday': betty_busy['Friday']
    }
    
    for day, betty_slots in days.items():
        megan_slots = megan_busy[day]
        for hour in range(work_start, work_end - meeting_duration + 1):
            slot_start = hour
            slot_end = hour + meeting_duration
            
            if is_slot_available(slot_start, slot_end, betty_slots) and is_slot_available(slot_start, slot_end, megan_slots):
                return f"{slot_start:02}:{slot_start+meeting_duration:02} {day}"
    return "No available time found"

# Define busy times for Betty and Megan
betty_busy = {
    'Monday': parse_busy_times("10:00 to 10:30, 11:30 to 12:30, 16:00 to 16:30"),
    'Tuesday': parse_busy_times("9:30 to 10:00, 10:30 to 11:00, 12:00 to 12:30, 13:30 to 15:00, 16:30 to 17:00"),
    'Wednesday': parse_busy_times("13:30 to 14:00, 14:30 to 15:00"),
    'Friday': parse_busy_times("9:00 to 10:00, 11:30 to 12:00, 12:30 to 13:00, 14:30 to 15:00")
}

megan_busy = {
    'Monday': parse_busy_times("9:00 to 17:00"),
    'Tuesday': parse_busy_times("9:00 to 9:30, 10:00 to 10:30, 12:00 to 14:00, 15:00 to 15:30, 16:00 to 16:30"),
    'Wednesday': parse_busy_times("9:30 to 10:30, 11:00 to 11:30, 12:30 to 13:00, 13:30 to 14:30, 15:30 to 17:00"),
    'Thursday': parse_busy_times("9:00 to 10:30, 11:30 to 14:00, 14:30 to 15:00, 15:30 to 16:30"),
    'Friday': parse_busy_times("9:00 to 17:00")
}

# Find and print the meeting time
meeting_time = find_meeting_time(betty_busy, megan_busy)
print(meeting_time)