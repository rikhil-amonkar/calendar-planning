from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration):
    # Define the work hours and days
    work_hours = [(9, 17)]
    work_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    # Sort the days based on the preference to avoid meetings on Wednesday
    work_days = sorted(work_days, key=lambda x: 1 if x == "Wednesday" else 0)

    # Iterate over each day
    for day in work_days:
        # Initialize the start time
        start_time = (9, 0)

        # Iterate over each hour
        while start_time[0] < 17:
            # Check if the time is available for both participants
            if (day in ["Monday", "Tuesday", "Wednesday", "Thursday"] and
                start_time not in schedules[0][day] and
                start_time not in schedules[1][day]):
                # Check if the meeting duration fits in the available time
                end_time = (start_time[0] + meeting_duration // 60, start_time[1] + meeting_duration % 60)
                if end_time <= (17, 0):
                    # Return the meeting time and day
                    return f"{start_time[0]:02d}:{start_time[1]:02d}-{end_time[0]:02d}:{end_time[1]:02d} on {day}"

            # Move to the next hour
            start_time = (start_time[0] + 1, 0)

    # If no available time is found, return a message
    return "No available time found"

# Define the schedules
schedules = [
    {
        "Monday": [(10, 30), (11, 0), (12, 30), (13, 0), (14, 30), (15, 30), (16, 0), (17, 0)],
        "Tuesday": [(9, 30), (10, 0), (11, 0), (11, 30), (13, 0), (13, 30), (14, 30), (15, 0), (16, 0), (17, 0)],
        "Wednesday": [(11, 30), (12, 0), (12, 30), (15, 30), (16, 30)],
        "Thursday": [(10, 30), (11, 0), (12, 0), (13, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
    },
    {
        "Monday": [(9, 0), (17, 0)],
        "Tuesday": [(9, 0), (11, 0), (11, 30), (13, 0), (13, 30), (14, 0), (14, 30), (16, 0), (17, 0)],
        "Wednesday": [(9, 0), (10, 0), (11, 0), (12, 0), (16, 0), (16, 30), (17, 0)],
        "Thursday": [(9, 0), (10, 30), (11, 0), (12, 30), (13, 0), (17, 0)]
    }
]

# Define the meeting duration
meeting_duration = 60

# Find the meeting time
meeting_time = find_meeting_time(schedules, meeting_duration)

# Print the meeting time
print(meeting_time)