def find_meeting_time(participants_schedules, day, work_hours, duration):
    start_hour, end_hour = work_hours
    # Convert work hours to minutes
    start_time = start_hour * 60
    end_time = end_hour * 60
    
    # Initialize a list to keep track of busy times for all participants
    busy_slots = []
    
    for schedule in participants_schedules:
        for meeting in schedule:
            start = meeting[0] * 60 + meeting[1]
            end = meeting[2] * 60 + meeting[3]
            busy_slots.append((start, end))
    
    # Sort all busy slots by start time
    busy_slots.sort()
    
    # Find available slots by checking gaps between busy slots
    available_slots = []
    previous_end = start_time
    
    for start, end in busy_slots:
        if start > previous_end:
            available_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    # Check the slot after the last busy slot
    if previous_end < end_time:
        available_slots.append((previous_end, end_time))
    
    # Find the first available slot that can fit the meeting duration
    for slot in available_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to hours and minutes
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            return (start_hh, start_mm, end_hh, end_mm)
    
    return None

# Define participants' schedules in (HH, MM, HH, MM) format
danielle_schedule = [
    (9, 0, 10, 0),
    (10, 30, 11, 0),
    (14, 30, 15, 0),
    (15, 30, 16, 0),
    (16, 30, 17, 0)
]

bruce_schedule = [
    (11, 0, 11, 30),
    (12, 30, 13, 0),
    (14, 0, 14, 30),
    (15, 30, 16, 0)
]

eric_schedule = [
    (9, 0, 9, 30),
    (10, 0, 11, 0),
    (11, 30, 13, 0),
    (14, 30, 15, 30)
]

participants_schedules = [danielle_schedule, bruce_schedule, eric_schedule]
day = "Monday"
work_hours = (9, 17)  # 9:00 to 17:00
duration = 60  # 1 hour in minutes

meeting_time = find_meeting_time(participants_schedules, day, work_hours, duration)

if meeting_time:
    start_hh, start_mm, end_hh, end_mm = meeting_time
    print(f"{day}: {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
else:
    print("No suitable meeting time found.")