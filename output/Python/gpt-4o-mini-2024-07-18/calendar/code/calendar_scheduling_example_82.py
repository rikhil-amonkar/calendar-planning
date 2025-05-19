from datetime import datetime, timedelta

def find_meeting_time(participants_schedules, meeting_duration, work_hours, day_of_week):
    # Convert meeting duration to timedelta
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Generate the available time slots based on work hours
    start_work = datetime.strptime(work_hours[0], "%H:%M")
    end_work = datetime.strptime(work_hours[1], "%H:%M")
    
    # Initialize available time slots
    available_slots = [(start_work, end_work)]
    
    # Iterate through each participant's schedule
    for schedule in participants_schedules:
        new_available_slots = []
        for start, end in available_slots:
            slot_start = start
            while slot_start < end:
                slot_end = slot_start + meeting_duration
                if slot_end > end:
                    break
                if not any(start < slot_end and slot_start < end for start, end in schedule):
                    new_available_slots.append((slot_start, slot_end))
                slot_start += timedelta(minutes=1)  # Increment slot start by 1 minute
        available_slots = new_available_slots
    
    # Return the first available slot
    if available_slots:
        start_time, end_time = available_slots[0]
        return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}", day_of_week
    return None

# Existing schedules
michael_schedule = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                    (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

eric_schedule = []  # Eric is available all day

arthur_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                   (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                   (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                   (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Participants' schedules
participants_schedules = [michael_schedule, eric_schedule, arthur_schedule]

# Meeting duration and work hours
meeting_duration = 30  # in minutes
work_hours = ["09:00", "17:00"]
day_of_week = "Monday"

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours, day_of_week)
print(meeting_time)