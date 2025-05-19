def find_meeting_time(betty_busy, megan_busy, days, duration_hours=1, work_start=9, work_end=17):
    for day in days:
        # Initialize available time for the day
        betty_available = [(work_start * 60, work_end * 60)]
        megan_available = [(work_start * 60, work_end * 60)]
        
        # Subtract busy times for Betty
        for busy in betty_busy.get(day, []):
            start, end = busy
            start_min = int(start.split(':')[0]) * 60 + int(start.split(':')[1])
            end_min = int(end.split(':')[0]) * 60 + int(end.split(':')[1])
            new_available = []
            for slot in betty_available:
                if end_min <= slot[0] or start_min >= slot[1]:
                    new_available.append(slot)
                else:
                    if slot[0] < start_min:
                        new_available.append((slot[0], start_min))
                    if slot[1] > end_min:
                        new_available.append((end_min, slot[1]))
            betty_available = new_available
        
        # Subtract busy times for Megan
        for busy in megan_busy.get(day, []):
            start, end = busy
            start_min = int(start.split(':')[0]) * 60 + int(start.split(':')[1])
            end_min = int(end.split(':')[0]) * 60 + int(end.split(':')[1])
            new_available = []
            for slot in megan_available:
                if end_min <= slot[0] or start_min >= slot[1]:
                    new_available.append(slot)
                else:
                    if slot[0] < start_min:
                        new_available.append((slot[0], start_min))
                    if slot[1] > end_min:
                        new_available.append((end_min, slot[1]))
            megan_available = new_available
        
        # Find overlapping slots
        for b_slot in betty_available:
            for m_slot in megan_available:
                overlap_start = max(b_slot[0], m_slot[0])
                overlap_end = min(b_slot[1], m_slot[1])
                if overlap_end - overlap_start >= duration_hours * 60:
                    # Convert back to HH:MM format
                    start_hh = overlap_start // 60
                    start_mm = overlap_start % 60
                    end_hh = (overlap_start + duration_hours * 60) // 60
                    end_mm = (overlap_start + duration_hours * 60) % 60
                    return day, f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    return None, None

# Define busy times
betty_busy = {
    'Monday': [('10:00', '10:30'), ('11:30', '12:30'), ('16:00', '16:30')],
    'Tuesday': [('9:30', '10:00'), ('10:30', '11:00'), ('12:00', '12:30'), ('13:30', '15:00'), ('16:30', '17:00')],
    'Wednesday': [('13:30', '14:00'), ('14:30', '15:00')],
    'Friday': [('9:00', '10:00'), ('11:30', '12:00'), ('12:30', '13:00'), ('14:30', '15:00')]
}

megan_busy = {
    'Monday': [('9:00', '17:00')],
    'Tuesday': [('9:00', '9:30'), ('10:00', '10:30'), ('12:00', '14:00'), ('15:00', '15:30'), ('16:00', '16:30')],
    'Wednesday': [('9:30', '10:30'), ('11:00', '11:30'), ('12:30', '13:00'), ('13:30', '14:30'), ('15:30', '17:00')],
    'Thursday': [('9:00', '10:30'), ('11:30', '14:00'), ('14:30', '15:00'), ('15:30', '16:30')],
    'Friday': [('9:00', '17:00')]
}

# Days to check (excluding Wednesday and Thursday as per Betty's constraint)
days_to_check = ['Tuesday']

day, time_slot = find_meeting_time(betty_busy, megan_busy, days_to_check)
if day and time_slot:
    print(f"{day}, {time_slot}")
else:
    print("No suitable time found.")