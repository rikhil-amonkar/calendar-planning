from datetime import datetime, timedelta

# Define the work hours and participants' busy schedules
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

participants_busy_times = {
    "Stephen": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Brittany": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), work_end)],
    "Dorothy": [(work_start, datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), work_end)],
    "Rebecca": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), work_end)],
    "Jordan": [(work_start, datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Define meeting duration
meeting_duration = timedelta(minutes=30)

# Function to find available meeting time
def find_available_time(busy_times):
    # Create a list of all busy time intervals
    busy_intervals = []
    for times in busy_times.values():
        busy_intervals.extend(times)

    # Sort busy intervals
    busy_intervals.sort(key=lambda x: x[0])

    # Check for available slots
    current_start = work_start
    for start, end in busy_intervals:
        if current_start + meeting_duration <= start:
            return current_start
        current_start = max(current_start, end)

    if current_start + meeting_duration <= work_end:
        return current_start

    return None

# Find suitable time
meeting_start = find_available_time(participants_busy_times)

# Output the result
if meeting_start:
    meeting_end = meeting_start + meeting_duration
    print(f"{{{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}}}")
    print("Monday")