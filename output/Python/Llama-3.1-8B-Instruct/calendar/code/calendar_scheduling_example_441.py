from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration):
    # Define the work hours and day
    work_hours = [(9, 17)]
    work_day = "Monday"

    # Initialize the start time
    start_time = (9, 0)

    # Iterate over each hour
    while start_time[0] < 17:
        # Check if the time is available for all participants
        if all(start_time not in schedule[work_day] for schedule in schedules):
            # Check if the meeting duration fits in the available time
            end_time = (start_time[0] + meeting_duration // 60, start_time[1] + meeting_duration % 60)
            if end_time <= (17, 0):
                # Return the meeting time and day
                return f"{start_time[0]:02d}:{start_time[1]:02d}-{end_time[0]:02d}:{end_time[1]:02d} on {work_day}"

        # Move to the next hour
        start_time = (start_time[0] + 1, 0)

    # If no available time is found, return a message
    return "No available time found"

# Define the schedules
schedules = [
    {
        "Monday": [(11, 30), (12, 0), (14, 30), (15, 0)]
    },
    {
        "Monday": [(9, 0), (10, 0), (14, 0), (14, 30), (16, 0), (16, 30)]
    },
    {},
    {
        "Monday": [(9, 0), (11, 0), (12, 0), (13, 0), (14, 0), (16, 0), (16, 30), (17, 0)]
    },
    {
        "Monday": [(9, 0), (11, 0), (12, 0), (13, 0), (14, 0), (16, 0), (16, 30), (17, 0)]
    },
    {
        "Monday": [(9, 30), (10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (13, 0), (15, 0), (16, 0), (16, 30), (17, 0)]
    }
]

# Define the meeting duration
meeting_duration = 30

# Find the meeting time
meeting_time = find_meeting_time(schedules, meeting_duration)

# Print the meeting time
print(meeting_time)