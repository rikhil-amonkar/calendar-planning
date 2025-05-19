from datetime import datetime, timedelta

# Define working hours
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define existing meetings for Jennifer
jennifer_schedule = {
    "Monday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    "Tuesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    "Wednesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
}

# Calculate available times
for day in ["Monday", "Tuesday", "Wednesday"]:
    current_time = start_time
    # Check for meetings on this day
    if day in jennifer_schedule:
        busy_times = jennifer_schedule[day]
        busy_times.sort(key=lambda x: x[0])  # Sort by start time

        # Add end of busy time to find gaps
        for start, end in busy_times:
            # Check for free time before the next meeting
            while current_time + meeting_duration <= start:
                print(f"Proposed meeting on {day} from {current_time.strftime('%H:%M')} to {(current_time + meeting_duration).strftime('%H:%M')}")
                current_time += meeting_duration
            
            # Move Current time to the end of the busy time if it overlaps
            current_time = max(current_time, end)

        # Check remaining time after the last meeting
        if current_time + meeting_duration <= end_time:
            print(f"Proposed meeting on {day} from {current_time.strftime('%H:%M')} to {(current_time + meeting_duration).strftime('%H:%M')}")