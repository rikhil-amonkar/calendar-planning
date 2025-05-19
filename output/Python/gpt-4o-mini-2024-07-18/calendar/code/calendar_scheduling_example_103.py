from datetime import datetime, timedelta

# Participants' schedules
schedules = {
    "Diane": [(datetime(2023, 10, 2, 9, 30), datetime(2023, 10, 2, 10, 0)),
              (datetime(2023, 10, 2, 14, 30), datetime(2023, 10, 2, 15, 0))],
    "Jack": [(datetime(2023, 10, 2, 13, 30), datetime(2023, 10, 2, 14, 0)),
             (datetime(2023, 10, 2, 14, 30), datetime(2023, 10, 2, 15, 0))],
    "Eugene": [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 10, 0)),
               (datetime(2023, 10, 2, 10, 30), datetime(2023, 10, 2, 11, 30)),
               (datetime(2023, 10, 2, 12, 0), datetime(2023, 10, 2, 14, 30)),
               (datetime(2023, 10, 2, 15, 0), datetime(2023, 10, 2, 16, 30))],
    "Patricia": [(datetime(2023, 10, 2, 9, 30), datetime(2023, 10, 2, 10, 30)),
                 (datetime(2023, 10, 2, 11, 0), datetime(2023, 10, 2, 12, 0)),
                 (datetime(2023, 10, 2, 12, 30), datetime(2023, 10, 2, 14, 0)),
                 (datetime(2023, 10, 2, 15, 0), datetime(2023, 10, 2, 16, 30))]
}

# Meeting parameters
meeting_duration = timedelta(minutes=30)
work_start = datetime(2023, 10, 2, 9, 0)
work_end = datetime(2023, 10, 2, 17, 0)

# Find available slot
def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Create a list of busy times
    busy_times = []
    for busy_slots in schedules.values():
        busy_times.extend(busy_slots)

    # Sort busy times
    busy_times.sort()

    # Check for available slots
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        # Check if this time is busy
        time_slot_end = current_time + meeting_duration
        is_busy = any(start < time_slot_end and current_time < end for start, end in busy_times)
        
        if not is_busy:
            return current_time, time_slot_end
        
        current_time += timedelta(minutes=1)
    
    return None, None

meeting_start, meeting_end = find_meeting_time(schedules, meeting_duration, work_start, work_end)

# Format output
if meeting_start and meeting_end:
    print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}")
    print("Monday")