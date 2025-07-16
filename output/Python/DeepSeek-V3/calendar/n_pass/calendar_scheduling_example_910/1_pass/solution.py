from datetime import time

def find_meeting_time(bryan_schedule, nicholas_schedule, days, duration_hours=1):
    work_start = time(9, 0)
    work_end = time(17, 0)
    
    for day in days:
        # Get busy times for Bryan and Nicholas on the current day
        bryan_busy = bryan_schedule.get(day, [])
        nicholas_busy = nicholas_schedule.get(day, [])
        
        # Combine and sort all busy intervals
        all_busy = bryan_busy + nicholas_busy
        all_busy.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_start
        
        for busy_start, busy_end in all_busy:
            if busy_start > prev_end:
                free_slots.append((prev_end, busy_start))
            prev_end = max(prev_end, busy_end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for duration
        for slot_start, slot_end in free_slots:
            slot_duration = (slot_end.hour - slot_start.hour) * 60 + (slot_end.minute - slot_start.minute)
            if slot_duration >= duration_hours * 60:
                meeting_end = time(slot_start.hour + duration_hours, slot_start.minute)
                return day, slot_start, meeting_end
    
    return None, None, None

# Define schedules
bryan_schedule = {
    'Thursday': [(time(9, 30), time(10, 0)), (time(12, 30), time(13, 0))],
    'Friday': [(time(10, 30), time(11, 0)), (time(14, 0), time(14, 30))],
}

nicholas_schedule = {
    'Monday': [(time(11, 30), time(12, 0)), (time(13, 0), time(15, 30))],
    'Tuesday': [(time(9, 0), time(9, 30)), (time(11, 0), time(13, 30)), (time(14, 0), time(16, 30))],
    'Wednesday': [(time(9, 0), time(9, 30)), (time(10, 0), time(11, 0)), (time(11, 30), time(13, 30)), 
                  (time(14, 0), time(14, 30)), (time(15, 0), time(16, 30))],
    'Thursday': [(time(10, 30), time(11, 30)), (time(12, 0), time(12, 30)), (time(15, 0), time(15, 30)), 
                 (time(16, 30), time(17, 0))],
    'Friday': [(time(9, 0), time(10, 30)), (time(11, 0), time(12, 0)), (time(12, 30), time(14, 30)), 
               (time(15, 30), time(16, 0)), (time(16, 30), time(17, 0))],
}

# Preferences: Bryan avoids Tuesday, Nicholas avoids Monday and Thursday
days_to_check = ['Wednesday', 'Friday']  # Excluded Monday, Tuesday, Thursday based on preferences

day, start_time, end_time = find_meeting_time(bryan_schedule, nicholas_schedule, days_to_check)

if day:
    print(f"{day}: {start_time.hour:02d}:{start_time.minute:02d}:{end_time.hour:02d}:{end_time.minute:02d}")
else:
    print("No suitable time found.")