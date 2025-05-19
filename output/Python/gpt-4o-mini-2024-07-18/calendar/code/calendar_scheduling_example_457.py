from datetime import datetime, timedelta

# Participants' schedules: (start_time, end_time)
schedules = {
    "Andrea": [(datetime(2023, 10, 2, 9, 30), datetime(2023, 10, 2, 10, 30)),
                (datetime(2023, 10, 2, 13, 30), datetime(2023, 10, 2, 14, 30))],
    "Ruth": [(datetime(2023, 10, 2, 12, 30), datetime(2023, 10, 2, 13, 0)),
             (datetime(2023, 10, 2, 15, 0), datetime(2023, 10, 2, 15, 30))],
    "Steven": [(datetime(2023, 10, 2, 10, 0), datetime(2023, 10, 2, 10, 30)),
               (datetime(2023, 10, 2, 11, 0), datetime(2023, 10, 2, 11, 30)),
               (datetime(2023, 10, 2, 12, 0), datetime(2023, 10, 2, 12, 30)),
               (datetime(2023, 10, 2, 13, 30), datetime(2023, 10, 2, 14, 0)),
               (datetime(2023, 10, 2, 15, 0), datetime(2023, 10, 2, 16, 0))],
    "Grace": [],
    "Kyle": [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 9, 30)),
             (datetime(2023, 10, 2, 10, 30), datetime(2023, 10, 2, 12, 0)),
             (datetime(2023, 10, 2, 12, 30), datetime(2023, 10, 2, 13, 0)),
             (datetime(2023, 10, 2, 13, 30), datetime(2023, 10, 2, 15, 0)),
             (datetime(2023, 10, 2, 15, 30), datetime(2023, 10, 2, 16, 0)),
             (datetime(2023, 10, 2, 16, 30), datetime(2023, 10, 2, 17, 0))],
    "Elijah": [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 11, 0)),
               (datetime(2023, 10, 2, 11, 30), datetime(2023, 10, 2, 13, 0)),
               (datetime(2023, 10, 2, 13, 30), datetime(2023, 10, 2, 14, 0)),
               (datetime(2023, 10, 2, 15, 30), datetime(2023, 10, 2, 16, 0)),
               (datetime(2023, 10, 2, 16, 30), datetime(2023, 10, 2, 17, 0))],
    "Lori": [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 9, 30)),
             (datetime(2023, 10, 2, 10, 0), datetime(2023, 10, 2, 11, 30)),
             (datetime(2023, 10, 2, 12, 0), datetime(2023, 10, 2, 13, 30)),
             (datetime(2023, 10, 2, 14, 0), datetime(2023, 10, 2, 16, 0)),
             (datetime(2023, 10, 2, 16, 30), datetime(2023, 10, 2, 17, 0))]
}

meeting_duration = timedelta(minutes=30)
work_start = datetime(2023, 10, 2, 9, 0)
work_end = datetime(2023, 10, 2, 17, 0)

def is_time_available(start, end):
    for participant, busy_slots in schedules.items():
        for busy_start, busy_end in busy_slots:
            if busy_start < end and start < busy_end:
                return False
    return True

# Check for available slots
current_time = work_start
while current_time + meeting_duration <= work_end:
    if is_time_available(current_time, current_time + meeting_duration):
        proposed_start = current_time
        proposed_end = current_time + meeting_duration
        print(f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}, Monday")
        break
    current_time += timedelta(minutes=1)