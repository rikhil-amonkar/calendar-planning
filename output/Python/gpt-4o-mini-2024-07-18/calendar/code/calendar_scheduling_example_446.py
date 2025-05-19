from datetime import datetime, timedelta

# Function to check if a time slot is free for all participants
def is_time_free(start_time, end_time, schedules):
    for schedule in schedules:
        for busy_start, busy_end in schedule:
            if (start_time < busy_end) and (end_time > busy_start):
                return False
    return True

# Define the busy schedules of each participant as lists of tuples (start, end)
schedules = [
    [(9, 0), (9, 30)],   # Megan
    [(9, 0), (9, 30)],   # Christine
    [],                  # Gabriel
    [(11, 30), (12, 0)], # Sara
    [(9, 30), (10, 0)],  # Bruce
    [(10, 0), (15, 30)], # Kathryn
    [(9, 0), (9, 30)],   # Billy
    [(11, 0), (11, 30)], # Billy
    [(12, 0), (14, 0)],  # Billy
    [(14, 30), (15, 30)] # Billy
]

# Meeting duration in minutes
meeting_duration = 30
meeting_start_time = 9  # 9 AM
meeting_end_time = 17   # 5 PM

# Convert hour and minute into total minutes for easier calculation
def to_minutes(hour, minute):
    return hour * 60 + minute

# Generate available time slots
available_slots = []
for hour in range(meeting_start_time, meeting_end_time):
    for minute in [0, 30]:  # Checking the start of each half hour
        start_time = to_minutes(hour, minute)
        end_time = start_time + meeting_duration
        
        if end_time <= to_minutes(meeting_end_time, 0):  # Make sure end time is within work hours
            if is_time_free(start_time, end_time, schedules):
                available_slots.append((hour, minute))

# Choose the first available slot
if available_slots:
    proposed_time = available_slots[0]
    proposed_start = f"{proposed_time[0]:02}:{proposed_time[1]:02}"
    proposed_end = f"{proposed_time[0]:02}:{(proposed_time[1] + meeting_duration) % 60:02}"
    day_of_week = "Monday"
    print(f"{proposed_start}:{proposed_end} - {day_of_week}")