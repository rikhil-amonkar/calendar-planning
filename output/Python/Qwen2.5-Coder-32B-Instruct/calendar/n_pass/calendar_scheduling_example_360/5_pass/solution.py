from datetime import datetime, timedelta

# Define a base date to use for all times
base_date = datetime(2023, 10, 1)  # Arbitrary date, just needs to be consistent

# Define the workday start and end times
workday_start = datetime.combine(base_date, datetime.strptime("09:00", "%H:%M").time())
workday_end = datetime.combine(base_date, datetime.strptime("17:00", "%H:%M").time())

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Emily": [
        (datetime.combine(base_date, datetime.strptime("10:00", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("10:30", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("16:00", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("16:30", "%H:%M").time()))
    ],
    "Mason": [],
    "Maria": [
        (datetime.combine(base_date, datetime.strptime("10:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("11:00", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("14:00", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("14:30", "%H:%M").time()))
    ],
    "Carl": [
        (datetime.combine(base_date, datetime.strptime("09:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("10:00", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("10:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("12:30", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("13:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("14:00", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("14:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("15:30", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("16:00", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("17:00", "%H:%M").time()))
    ],
    "David": [
        (datetime.combine(base_date, datetime.strptime("09:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("11:00", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("11:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("12:00", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("12:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("13:30", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("14:00", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("15:00", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("16:00", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("17:00", "%H:%M").time()))
    ],
    "Frank": [
        (datetime.combine(base_date, datetime.strptime("09:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("10:30", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("11:00", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("11:30", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("12:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("13:30", "%H:%M").time())),
        (datetime.combine(base_date, datetime.strptime("14:30", "%H:%M").time()), 
         datetime.combine(base_date, datetime.strptime("17:00", "%H:%M").time()))
    ]
}

# Convert busy times to datetime objects
for person, busy in busy_times.items():
    busy_times[person] = [(datetime.combine(base_date, start.time()), datetime.combine(base_date, end.time())) for start, end in busy]

# Function to check if a time slot is available for all participants
def is_time_slot_available(time_slot):
    for person, busy in busy_times.items():
        for busy_start, busy_end in busy:
            if busy_start <= time_slot[1] and busy_end >= time_slot[0]:
                return False
    return True

# Find a suitable time slot
current_time = workday_start
while current_time + meeting_duration <= workday_end:
    time_slot = (current_time, current_time + meeting_duration)
    if is_time_slot_available(time_slot):
        # Output the found time slot and day of the week
        print(f"{time_slot[0].strftime('%H:%M')}-{time_slot[1].strftime('%H:%M')}:Monday")
        break
    current_time += timedelta(minutes=30)