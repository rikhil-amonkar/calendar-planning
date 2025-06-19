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

        # Iterate over each scheduled event
        for start, end in nancy_schedule[day]:
            for start_j, end_j in jose_schedule[day]:
                # Calculate the start time of the meeting
                start_time = max(start, start_j)

                # Check if the meeting starts within the work hours
                if start_time < start_hour:
                    start_time = start_hour

                # Check if the meeting starts within the end of the work hours
                if start_time + meeting_duration > end_hour:
                    start_time = end_hour - meeting_duration

                # Calculate the end time of the meeting
                end_time = start_time + meeting_duration

                # Check if the meeting time is available in both schedules
                hour_available = True
                for n_start, n_end in nancy_schedule[day]:
                    if start_time < n_end and end_time > n_start:
                        hour_available = False
                        break
                for j_start, j_end in jose_schedule[day]:
                    if start_time < j_end and end_time > j_start:
                        hour_available = False
                        break

                # If the meeting time is available, print the meeting time
                if hour_available:
                    print(f"{day}: {start_time:02d}:00 - {end_time:02d}:00")
                    meeting_time_found = True

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