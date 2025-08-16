from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, day_of_week):
    # Convert times to datetime objects for easier manipulation
    def parse_schedule(schedule):
        return [tuple(datetime.strptime(t, "%H:%M") for t in slot) for slot in schedule]

    # Margaret's schedule
    margaret_schedule = parse_schedule([
        ("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:00"),
        ("13:00", "13:30"), ("15:00", "15:30")
    ])
    
    # Donna's schedule
    donna_schedule = parse_schedule([
        ("14:30", "15:00"), ("16:00", "16:30")
    ])
    
    # Helen's schedule
    helen_schedule = parse_schedule([
        ("09:00", "09:30"), ("10:00", "11:30"), ("13:00", "14:00"),
        ("14:30", "15:00"), ("15:30", "17:00")
    ])

    # Combine all schedules
    all_schedules = margaret_schedule + donna_schedule + helen_schedule
    
    # Sort the combined schedule by start time
    all_schedules.sort()

    # Define the work day boundaries
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")

    # Initialize the current time to the start of the work day
    current_time = work_start

    # Check for available slots
    while current_time < work_end - timedelta(minutes=meeting_duration):
        next_event = min(
            (event for event in all_schedules if event[0] >= current_time),
            default=(work_end, work_end)
        )
        
        # Calculate the free slot duration
        free_slot_duration = next_event[0] - current_time
        
        # If the free slot is large enough for the meeting, propose it
        if free_slot_duration.total_seconds() / 60 >= meeting_duration:
            meeting_start = current_time
            meeting_end = meeting_start + timedelta(minutes=meeting_duration)
            return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day_of_week
        
        # Move the current time to the end of the next event
        current_time = next_event[1]

# Constraints
participants = ["Margaret", "Donna", "Helen"]
meeting_duration = 30  # in minutes
day_of_week = "Monday"

# Find and print the meeting time
meeting_time, meeting_day = find_meeting_time(participants, meeting_duration, day_of_week)
print(meeting_time, meeting_day)