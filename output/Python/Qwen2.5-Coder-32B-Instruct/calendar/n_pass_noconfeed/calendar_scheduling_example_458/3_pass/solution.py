from datetime import datetime, timedelta

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the participants' availability
availability = {
    "Wayne": [(work_start, work_end)],
    "Melissa": [
        (work_start, datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), work_end)
    ],
    "Catherine": [(work_start, work_end)],
    "Gregory": [
        (work_start, datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), work_end)
    ],
    "Victoria": [
        (datetime.strptime("9:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), work_end)
    ],
    "Thomas": [
        (work_start, datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), work_end)
    ],
    "Jennifer": [
        (datetime.strptime("9:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), work_end)
    ]
}

# Wayne's preference
wayne_preference_start = datetime.strptime("14:00", "%H:%M")

# Function to find a suitable meeting time
def find_meeting_time(availability, meeting_duration, work_start, work_end):
    # Iterate over all possible start times from work start to work end minus meeting duration
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        # Check if all participants are available at this time
        available_for_all = True
        for person, slots in availability.items():
            person_available = False
            for start, end in slots:
                if start <= current_time < end - meeting_duration:
                    person_available = True
                    break
            if not person_available:
                available_for_all = False
                break
        if available_for_all:
            return current_time, current_time + meeting_duration
        current_time += timedelta(minutes=15)  # Check every 15 minutes for better granularity
    return None, None  # Return None if no suitable time is found

# Find the meeting time
meeting_start, meeting_end = find_meeting_time(availability, meeting_duration, work_start, work_end)

# Output the result
if meeting_start and meeting_end:
    print(f"Meeting scheduled from {meeting_start.strftime('%H:%M')} to {meeting_end.strftime('%H:%M')}, Monday")
else:
    print("No suitable meeting time found.")