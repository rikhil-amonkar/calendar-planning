from datetime import datetime, timedelta

# Function to check availability of the participants
def is_available(start_time, end_time, busy_slots):
    for start, end in busy_slots:
        if start_time < end and start < end_time:
            return False
    return True

# Define the schedules
eugene_busy = [(datetime(2023, 10, 2, 11, 0), datetime(2023, 10, 2, 12, 0)),
               (datetime(2023, 10, 2, 13, 30), datetime(2023, 10, 2, 14, 0)),
               (datetime(2023, 10, 2, 14, 30), datetime(2023, 10, 2, 15, 0)),
               (datetime(2023, 10, 2, 16, 0), datetime(2023, 10, 2, 16, 30)),
               (datetime(2023, 10, 4, 9, 0), datetime(2023, 10, 4, 9, 30)),
               (datetime(2023, 10, 4, 11, 0), datetime(2023, 10, 4, 11, 30)),
               (datetime(2023, 10, 4, 12, 0), datetime(2023, 10, 4, 12, 30)),
               (datetime(2023, 10, 4, 13, 30), datetime(2023, 10, 4, 15, 0)),
               (datetime(2023, 10, 5, 9, 30), datetime(2023, 10, 5, 10, 0)),
               (datetime(2023, 10, 5, 11, 0), datetime(2023, 10, 5, 12, 30)),
               (datetime(2023, 10, 6, 10, 30), datetime(2023, 10, 6, 11, 0)),
               (datetime(2023, 10, 6, 12, 0), datetime(2023, 10, 6, 12, 30)),
               (datetime(2023, 10, 6, 13, 0), datetime(2023, 10, 6, 13, 30))]

eric_busy = [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 17, 0)),
              (datetime(2023, 10, 3, 9, 0), datetime(2023, 10, 3, 17, 0)),
              (datetime(2023, 10, 4, 9, 0), datetime(2023, 10, 4, 11, 30)),
              (datetime(2023, 10, 4, 12, 0), datetime(2023, 10, 4, 14, 0)),
              (datetime(2023, 10, 4, 14, 30), datetime(2023, 10, 4, 16, 30)),
              (datetime(2023, 10, 5, 9, 0), datetime(2023, 10, 5, 17, 0)),
              (datetime(2023, 10, 6, 9, 0), datetime(2023, 10, 6, 11, 0)),
              (datetime(2023, 10, 6, 11, 30), datetime(2023, 10, 6, 17, 0))]

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Check for availability
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    for hour in range(9, 17):
        start_time = datetime(2023, 10, 2 if day == 'Monday' else 3 if day == 'Tuesday' else 4 if day == 'Wednesday' else 5 if day == 'Thursday' else 6, hour, 0)
        end_time = start_time + meeting_duration
        if is_available(start_time, end_time, eugene_busy) and is_available(start_time, end_time, eric_busy):
            print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
            break