from datetime import datetime, timedelta

def is_free(start_time, end_time, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

def schedule_meeting(participants, meeting_duration_minutes):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    delta = timedelta(minutes=meeting_duration_minutes)
    
    for hour in range(9, 17):
        for minute in range(0, 60, 30):
            start_time = datetime(2023, 1, 1, hour, minute)
            end_time = start_time + delta
            if end_time > work_end:
                continue
            all_free = True
            for name, intervals in participants.items():
                if not is_free(start_time, end_time, intervals):
                    all_free = False
                    break
            if all_free:
                return start_time.strftime("%H:%M") + ":" + end_time.strftime("%H:%M"), "Monday"
    return None, None

# Define participants and their busy intervals (in 24-hour format)
participants = {
    "Emily": [(10, 0, 10, 30), (16, 0, 16, 30)],
    "Mason": [],
    "Maria": [(10, 30, 11, 0), (14, 0, 14, 30)],
    "Carl": [(9, 30, 10, 0), (10, 30, 12, 30), (13, 30, 14, 0), (14, 30, 15, 30), (16, 0, 17, 0)],
    "David": [(9, 30, 11, 0), (11, 30, 12, 0), (12, 30, 13, 30), (14, 0, 15, 0), (16, 0, 17, 0)],
    "Frank": [(9, 30, 10, 30), (11, 0, 11, 30), (12, 30, 13, 30), (14, 30, 17, 0)]
}

# Convert busy intervals to datetime objects for comparison
converted_participants = {}
for name, intervals in participants.items():
    converted_intervals = []
    for start_h, start_m, end_h, end_m in intervals:
        start = datetime(2023, 1, 1, start_h, start_m)
        end = datetime(2023, 1, 1, end_h, end_m)
        converted_intervals.append((start, end))
    converted_participants[name] = converted_intervals

# Schedule the meeting
time_range, day = schedule_meeting(converted_participants, 30)
print(f"{{ {time_range} }} {day}")