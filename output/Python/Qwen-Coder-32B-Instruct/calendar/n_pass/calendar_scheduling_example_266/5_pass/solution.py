from datetime import datetime, timedelta

def find_meeting_time(schedules, duration, start_time, end_time):
    # Convert times to minutes since start of the day for easier comparison
    start_minutes = start_time.hour * 60 + start_time.minute
    end_minutes = end_time.hour * 60 + end_time.minute
    duration_minutes = duration.seconds // 60
    
    # Initialize available time slots
    available_slots = set(range(start_minutes, end_minutes - duration_minutes + 1))
    
    # Remove unavailable slots based on each person's schedule
    for person_schedule in schedules:
        for event_start, event_end in person_schedule:
            event_start_minutes = event_start.hour * 60 + event_start.minute
            event_end_minutes = event_end.hour * 60 + event_end.minute
            for minute in range(event_start_minutes, event_end_minutes):
                if minute in available_slots:
                    available_slots.remove(minute)
    
    # Find the first available slot
    for start_minute in available_slots:
        end_minute = start_minute + duration_minutes
        if all(minute in available_slots for minute in range(start_minute, end_minute)):
            meeting_start = start_time + timedelta(minutes=start_minute)
            meeting_end = meeting_start + duration
            return f"{meeting_start.hour:02}:{meeting_start.minute:02}-{meeting_end.hour:02}:{meeting_end.minute:02}"
    
    return None

# Define the schedules in datetime objects
joe_schedule = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M"))]
keith_schedule = [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))]
patricia_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                     (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))]
nancy_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
pamela_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                   (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                   (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                   (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                   (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                   (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                   (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Combine all schedules
all_schedules = [joe_schedule, keith_schedule, patricia_schedule, nancy_schedule, pamela_schedule]

# Define meeting duration and work hours
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")  # Ensure the end time is before 17:00

# Find a suitable meeting time
meeting_time = find_meeting_time(all_schedules, meeting_duration, work_start, work_end)
if meeting_time:
    print(f"{meeting_time} Monday")
else:
    print("No available meeting time found.")