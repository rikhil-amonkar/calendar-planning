from datetime import datetime, timedelta

# Define work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Define existing schedules
judith_schedule = {
    'Monday': [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    'Wednesday': [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))],
}

timothy_schedule = {
    'Monday': [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    'Tuesday': [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    'Wednesday': [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
    ],
}

# Combine schedules and propose a meeting time
def find_meeting_time():
    # Check possible days
    possible_days = ['Monday', 'Tuesday', 'Wednesday']
    for day in possible_days:
        # Get busy times
        busy_times = judith_schedule.get(day, []) + timothy_schedule.get(day, [])
        busy_times.sort()  # Sort busy times by start time

        # Find available slot
        current_time = work_start
        for start, end in busy_times:
            # Check for available time before the busy slot
            if current_time + meeting_duration <= start:
                return f"{day}: {current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}"
            current_time = max(current_time, end)

        # Check for availability after the last busy slot until work end
        if current_time + meeting_duration <= work_end:
            return f"{day}: {current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}"

    return "No available time found"

# Call function to get proposed meeting time
proposed_time = find_meeting_time()
print(proposed_time)