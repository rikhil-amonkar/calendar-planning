def find_meeting_time(participants_schedules, duration, work_hours_start, work_hours_end):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Initialize the free slots as the entire work day
    free_slots = [(work_start, work_end)]
    
    # Function to subtract busy slots from free slots
    def subtract_busy(free_slots, busy_start, busy_end):
        new_free_slots = []
        for start, end in free_slots:
            if busy_start >= end or busy_end <= start:
                new_free_slots.append((start, end))
            else:
                if start < busy_start:
                    new_free_slots.append((start, busy_start))
                if end > busy_end:
                    new_free_slots.append((busy_end, end))
        return new_free_slots
    
    # Process each participant's schedule
    for schedule in participants_schedules:
        for busy_start_str, busy_end_str in schedule:
            busy_start = time_to_minutes(busy_start_str)
            busy_end = time_to_minutes(busy_end_str)
            free_slots = subtract_busy(free_slots, busy_start, busy_end)
    
    # Find the first slot that can fit the meeting duration
    for start, end in free_slots:
        if end - start >= duration:
            meeting_end = start + duration
            return (minutes_to_time(start), minutes_to_time(meeting_end))
    
    return None

# Define the participants' schedules
danielle_schedule = [
    ("09:00", "10:00"),
    ("10:30", "11:00"),
    ("14:30", "15:00"),
    ("15:30", "16:00"),
    ("16:30", "17:00")
]

bruce_schedule = [
    ("11:00", "11:30"),
    ("12:30", "13:00"),
    ("14:00", "14:30"),
    ("15:30", "16:00")
]

eric_schedule = [
    ("09:00", "09:30"),
    ("10:00", "11:00"),
    ("11:30", "13:00"),
    ("14:30", "15:30")
]

participants_schedules = [danielle_schedule, bruce_schedule, eric_schedule]
meeting_duration = 60  # minutes
work_hours_start = "09:00"
work_hours_end = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No suitable time found.")