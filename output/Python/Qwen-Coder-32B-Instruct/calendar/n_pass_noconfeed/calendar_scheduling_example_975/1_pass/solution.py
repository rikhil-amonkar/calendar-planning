from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Define the schedules
nicole_schedule = {
    'Tuesday': [datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")],
    'Wednesday': [datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")],
    'Friday': [
        datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
        datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")
    ]
}

daniel_schedule = {
    'Monday': [
        datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
        datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
        datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")
    ],
    'Tuesday': [
        datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M"),
        datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
        datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
        datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M"),
        datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")
    ],
    'Wednesday': [
        datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M"),
        datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
        datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
        datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"),
        datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")
    ],
    'Thursday': [
        datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M"),
        datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M"),
        datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")
    ],
    'Friday': [
        datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M"),
        datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"),
        datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:30", "%H:%M"),
        datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"),
        datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")
    ]
}

# Function to check if a time slot is available for both participants
def is_slot_available(day, start_time):
    end_time = start_time + meeting_duration
    
    # Check Nicole's schedule
    if day in nicole_schedule:
        for n_start, n_end in zip(nicole_schedule[day][::2], nicole_schedule[day][1::2]):
            if not (end_time <= n_start or start_time >= n_end):
                return False
    
    # Check Daniel's schedule
    if day in daniel_schedule:
        for d_start, d_end in zip(daniel_schedule[day][::2], daniel_schedule[day][1::2]):
            if not (end_time <= d_start or start_time >= d_end):
                return False
    
    return True

# Find the earliest available time slot
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_available(day, current_time):
            start_time_str = current_time.strftime("%H:%M")
            end_time_str = (current_time + meeting_duration).strftime("%H:%M")
            print(f"{start_time_str}:{end_time_str} {day}")
            break
        current_time += timedelta(minutes=30)