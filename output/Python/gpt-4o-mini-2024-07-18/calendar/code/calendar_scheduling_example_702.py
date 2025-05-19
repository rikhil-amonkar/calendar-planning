from datetime import datetime, timedelta

# Define the participants' schedules
robert_schedule = {
    'Monday': [
        ("11:00", "11:30"),
        ("14:00", "14:30"),
        ("15:30", "16:00"),
    ],
    'Tuesday': [
        ("10:30", "11:00"),
        ("15:00", "15:30"),
    ],
    'Wednesday': [
        ("10:00", "11:00"),
        ("11:30", "12:00"),
        ("12:30", "13:00"),
        ("13:30", "14:00"),
        ("15:00", "15:30"),
        ("16:00", "16:30"),
    ]
}

ralph_schedule = {
    'Monday': [
        ("10:00", "13:30"),
        ("14:00", "14:30"),
        ("15:00", "17:00"),
    ],
    'Tuesday': [
        ("9:00", "9:30"),
        ("10:00", "10:30"),
        ("11:00", "11:30"),
        ("12:00", "13:00"),
        ("14:00", "15:30"),
        ("16:00", "17:00"),
    ],
    'Wednesday': [
        ("10:30", "11:00"),
        ("11:30", "12:00"),
        ("13:00", "14:30"),
        ("16:30", "17:00"),
    ]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Function to find available meeting time
def find_meeting_time():
    for day in ['Tuesday', 'Wednesday']:  # Start with preferred days
        robert_busy_times = robert_schedule[day]
        ralph_busy_times = ralph_schedule[day]
        
        # Create a list of busy times merged for both participants
        busy_times = robert_busy_times + ralph_busy_times
        
        # Convert times to datetime and sort
        busy_times = sorted([(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in busy_times])
        
        # Find time slots for meeting within work hours (9:00 to 17:00)
        current_time = datetime.strptime("09:00", "%H:%M")
        end_of_work_day = datetime.strptime("17:00", "%H:%M")
        
        for start, end in busy_times:
            # Check for the gap before the busy time
            if current_time + meeting_duration <= start:
                return f'{day} {current_time.time()} {current_time + meeting_duration.time()}'
            
            # Move current time to the end of the busy period
            if current_time < end:
                current_time = end

        # Final check after the last busy time until end of work day
        if current_time + meeting_duration <= end_of_work_day:
            return f'{day} {current_time.time()} {current_time + meeting_duration.time()}'

# Run function and print the proposed time for the meeting
print(find_meeting_time())