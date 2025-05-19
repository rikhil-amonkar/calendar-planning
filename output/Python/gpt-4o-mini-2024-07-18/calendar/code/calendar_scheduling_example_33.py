from datetime import datetime, timedelta

# Define the work hours and the meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)
day_of_week = "Monday"

# Define the schedules of each participant as busy time slots
schedules = {
    "Lisa": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
             (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
             (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Bobby": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Randy": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Find a suitable time for the meeting
def find_meeting_time(schedules, work_start, work_end, meeting_duration):
    free_slots = []

    current_time = work_start
    while current_time + meeting_duration <= work_end:
        end_time = current_time + meeting_duration
        is_free = True

        for busy_times in schedules.values():
            for start, end in busy_times:
                if not (end_time <= start or current_time >= end):
                    is_free = False
                    break
            if not is_free:
                break
        
        if is_free:
            free_slots.append((current_time, end_time))
        
        current_time += timedelta(minutes=15)  # check every 15 minutes

    # Select a free slot that satisfies Bobby's preference
    for start, end in free_slots:
        if start.time() >= datetime.strptime("15:00", "%H:%M").time():
            continue
        return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}"

# Call function to get the meeting time
meeting_time = find_meeting_time(schedules, work_start, work_end, meeting_duration)

print(f"Proposed Meeting Time: {meeting_time}, Day: {day_of_week}")