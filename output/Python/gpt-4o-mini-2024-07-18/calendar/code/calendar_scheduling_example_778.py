from datetime import datetime, timedelta

# Define participants' schedules
susan_schedule = {
    "Monday": [(9, 0, 12, 30), (13, 30, 14, 0)],
    "Tuesday": [(11, 30, 12, 0)],
    "Wednesday": [(9, 30, 10, 30), (14, 0, 14, 30), (15, 30, 16, 30)]
}

sandra_schedule = {
    "Monday": [(9, 0, 13, 0), (14, 0, 15, 0), (16, 0, 16, 30)],
    "Tuesday": [(9, 0, 9, 30), (10, 30, 12, 0), (12, 30, 13, 30), (14, 0, 14, 30), (16, 0, 17, 0)],
    "Wednesday": [(9, 0, 11, 30), (12, 0, 12, 30), (13, 0, 17, 0)]
}

# Function to find possible meeting times
def find_meeting_time(susan_schedule, sandra_schedule, duration_minutes, preferred_days):
    duration = timedelta(minutes=duration_minutes)
    
    for day in preferred_days:
        susan_busy_times = susan_schedule.get(day, [])
        sandra_busy_times = sandra_schedule.get(day, [])

        # Create list of busy times with tuples of start and end times
        busy_times = []

        # Convert busy times to datetime objects for ease of comparison
        for start_hour, start_minute, end_hour, end_minute in susan_busy_times + sandra_busy_times:
            busy_times.append((datetime(2000, 1, 1, start_hour, start_minute),
                                datetime(2000, 1, 1, end_hour, end_minute)))
        
        # Sort busy times by start time
        busy_times.sort()

        # Availability starts at 9:00
        available_start = datetime(2000, 1, 1, 9, 0)
        # Availability ends at 17:00
        available_end = datetime(2000, 1, 1, 17, 0)

        for start, end in busy_times:
            if available_start + duration <= start:
                # If there is a gap between available time and busy time
                if available_start + duration <= available_end:
                    return f"{day} {available_start.strftime('%H:%M')}:{(available_start + duration).strftime('%H:%M')}"

            # Shift available start time to the end of the current busy time
            available_start = max(available_start, end)

        # Check if there's remaining time after the last busy slot
        if available_start + duration <= available_end:
            return f"{day} {available_start.strftime('%H:%M')}:{(available_start + duration).strftime('%H:%M')}"

# Define meeting duration and preferred days
meeting_duration = 30  # in minutes
preferred_days = ["Wednesday"]

# Find and print the meeting time
meeting_time = find_meeting_time(susan_schedule, sandra_schedule, meeting_duration, preferred_days)
print(meeting_time)