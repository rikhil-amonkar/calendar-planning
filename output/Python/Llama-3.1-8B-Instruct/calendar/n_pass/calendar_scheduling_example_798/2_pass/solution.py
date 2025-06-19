from datetime import datetime, timedelta

def find_meeting_time(nancy_schedule, jose_schedule, meeting_duration):
    # Define the work hours
    start_hour = 9
    end_hour = 17

    # Define the days
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Iterate over each day
    for day in days:
        # Initialize a flag to indicate if a meeting time is found
        meeting_time_found = False

        # Iterate over each hour
        for hour in range(start_hour, end_hour):
            # Initialize a flag to indicate if the hour is available for both participants
            hour_available = True

            # Check Nancy's schedule
            for start, end in nancy_schedule[day]:
                if start <= hour < end:
                    hour_available = False
                    break

            # Check Jose's schedule
            for start, end in jose_schedule[day]:
                if start <= hour < end:
                    hour_available = False
                    break

            # If the hour is available, check if there is enough time for the meeting
            if hour_available:
                # Calculate the end time of the meeting
                end_time = hour + meeting_duration

                # Check if the end time is within the work hours
                if end_time <= end_hour:
                    # Check Nancy's schedule
                    for start, end in nancy_schedule[day]:
                        if start <= end_time < end:
                            hour_available = False
                            break

                    # Check Jose's schedule
                    for start, end in jose_schedule[day]:
                        if start <= end_time < end:
                            hour_available = False
                            break

                    # If the hour is still available, print the meeting time
                    if hour_available:
                        print(f"{day}: {hour:02d}:00 - {end_time:02d}:00")
                        meeting_time_found = True
                        break

        # If a meeting time is found, break the loop
        if meeting_time_found:
            break

# Define the schedules
nancy_schedule = {
    'Monday': [(10, 10), (11, 12), (13, 14), (14, 15), (16, 17)],
    'Tuesday': [(9, 10), (11, 11), (12, 12), (13, 13), (15, 16)],
    'Wednesday': [(10, 11), (13, 16)]
}

jose_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 9), (10, 12), (13, 14), (15, 17)]
}

# Define the meeting duration
meeting_duration = 30

find_meeting_time(nancy_schedule, jose_schedule, meeting_duration)