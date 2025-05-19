from datetime import datetime, timedelta

# Define the participants' schedules
schedules = {
    'Joe': [(datetime(2023, 10, 2, 9, 30), datetime(2023, 10, 2, 10, 0)),
            (datetime(2023, 10, 2, 10, 30), datetime(2023, 10, 2, 11, 0))],
    'Keith': [(datetime(2023, 10, 2, 11, 30), datetime(2023, 10, 2, 12, 0)),
              (datetime(2023, 10, 2, 15, 0), datetime(2023, 10, 2, 15, 30))],
    'Patricia': [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 9, 30)),
                 (datetime(2023, 10, 2, 13, 0), datetime(2023, 10, 2, 13, 30))],
    'Nancy': [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 11, 0)),
              (datetime(2023, 10, 2, 11, 30), datetime(2023, 10, 2, 16, 30))],
    'Pamela': [(datetime(2023, 10, 2, 9, 0), datetime(2023, 10, 2, 10, 0)),
               (datetime(2023, 10, 2, 10, 30), datetime(2023, 10, 2, 11, 0)),
               (datetime(2023, 10, 2, 11, 30), datetime(2023, 10, 2, 12, 30)),
               (datetime(2023, 10, 2, 13, 0), datetime(2023, 10, 2, 14, 0)),
               (datetime(2023, 10, 2, 14, 30), datetime(2023, 10, 2, 15, 0)),
               (datetime(2023, 10, 2, 15, 30), datetime(2023, 10, 2, 16, 0)),
               (datetime(2023, 10, 2, 16, 30), datetime(2023, 10, 2, 17, 0))]
}

# Define work hours
work_start = datetime(2023, 10, 2, 9, 0)
work_end = datetime(2023, 10, 2, 17, 0)
meeting_duration = timedelta(minutes=30)

# Function to find a suitable time for the meeting
def find_meeting_time(schedules):
    # Create a list of blocks from all schedules
    busy_times = []
    for participant, blocks in schedules.items():
        busy_times.extend(blocks)
    
    # Sort the busy times
    busy_times.sort()

    # Check for free time slots within work hours
    current_time = work_start
    for start, end in busy_times:
        if current_time + meeting_duration <= start:
            return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} on Monday"
        current_time = max(current_time, end)

    # Final check for the remaining time slot after last busy time
    if current_time + meeting_duration <= work_end:
        return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} on Monday"

# Get the proposed meeting time
proposed_time = find_meeting_time(schedules)
print(proposed_time)