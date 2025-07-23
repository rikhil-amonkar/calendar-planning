def find_meeting_time(participants_schedules, day, work_hours, duration_minutes):
    # Parse work hours
    work_start, work_end = work_hours.split(" to ")
    work_start = int(work_start.split(":")[0]) * 60 + int(work_start.split(":")[1])
    work_end = int(work_end.split(":")[0]) * 60 + int(work_end.split(":")[1])
    
    # Initialize a list to represent the availability of each minute in the workday
    total_minutes = work_end - work_start
    availability = [True] * total_minutes
    
    # Process each participant's schedule
    for participant, meetings in participants_schedules.items():
        for meeting in meetings:
            start, end = meeting.split(" to ")
            start_min = (int(start.split(":")[0]) * 60 + int(start.split(":")[1])) - work_start
            end_min = (int(end.split(":")[0]) * 60 + int(end.split(":")[1])) - work_start
            # Mark the minutes during the meeting as unavailable
            for minute in range(start_min, end_min):
                if minute >= 0 and minute < total_minutes:
                    availability[minute] = False
    
    # Find the first available slot of the required duration
    required_slots = duration_minutes
    current_slot = 0
    for minute in range(total_minutes):
        if availability[minute]:
            current_slot += 1
            if current_slot >= required_slots:
                start_minute = minute - required_slots + 1
                start_time = work_start + start_minute
                end_time = start_time + required_slots
                # Convert back to HH:MM format
                start_hh = start_time // 60
                start_mm = start_time % 60
                end_hh = end_time // 60
                end_mm = end_time % 60
                return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
        else:
            current_slot = 0
    return None

# Define the participants' schedules
participants_schedules = {
    "Emily": ["10:00 to 10:30", "16:00 to 16:30"],
    "Mason": [],
    "Maria": ["10:30 to 11:00", "14:00 to 14:30"],
    "Carl": ["9:30 to 10:00", "10:30 to 12:30", "13:30 to 14:00", "14:30 to 15:30", "16:00 to 17:00"],
    "David": ["9:30 to 11:00", "11:30 to 12:00", "12:30 to 13:30", "14:00 to 15:00", "16:00 to 17:00"],
    "Frank": ["9:30 to 10:30", "11:00 to 11:30", "12:30 to 13:30", "14:30 to 17:00"]
}

# Define the meeting parameters
day = "Monday"
work_hours = "9:00 to 17:00"
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_hours, duration_minutes)

# Output the result
print(f"{day}: {meeting_time}")