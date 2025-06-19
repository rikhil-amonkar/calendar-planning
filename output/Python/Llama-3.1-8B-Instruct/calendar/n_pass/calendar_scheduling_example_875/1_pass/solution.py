from datetime import datetime, timedelta

def find_meeting_time(natalie_schedule, william_schedule, meeting_duration):
    # Define work hours
    start_hour = 9
    end_hour = 17

    # Iterate over all possible days
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
        # Initialize time
        hour = start_hour
        minute = 0

        # Iterate over all possible hours
        while hour < end_hour:
            # Check if time is available for both participants
            if (hour, minute) not in natalie_schedule.get(day, []) and \
               (hour, minute) not in william_schedule.get(day, []):
                # Check if there is enough time for the meeting
                end_time = (hour + meeting_duration // 60, minute + meeting_duration % 60)
                if end_time[0] <= end_hour and end_time[1] <= 59:
                    # Return the meeting time
                    return f"{day} {datetime(1900, 1, 1, hour, minute).strftime('%H:%M')} - {datetime(1900, 1, 1, end_time[0], end_time[1]).strftime('%H:%M')}"

            # Move to the next time slot
            minute += 30
            if minute >= 60:
                hour += 1
                minute = 0

    # If no time is found, return an error message
    return "No available time found"


# Define the schedules
natalie_schedule = {
    "Monday": [(9, 30), (10, 0), (12, 0), (12, 30), (14, 0), (14, 30), (15, 0), (16, 30)],
    "Tuesday": [(9, 0), (9, 30), (10, 0), (10, 30), (12, 30), (14, 0), (16, 0), (17, 0)],
    "Wednesday": [(11, 0), (11, 30), (16, 0), (16, 30)],
    "Thursday": [(10, 0), (11, 30), (11, 30), (15, 0), (15, 30), (16, 30), (17, 0)]
}

william_schedule = {
    "Monday": [(9, 30), (11, 0), (11, 30), (17, 0)],
    "Tuesday": [(9, 0), (9, 30), (13, 0), (13, 30), (16, 0)],
    "Wednesday": [(9, 0), (12, 30), (13, 0), (14, 30), (15, 30), (16, 30), (17, 0)],
    "Thursday": [(9, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (14, 0), (15, 0), (17, 0)]
}

meeting_duration = 60

# Find the meeting time
print(find_meeting_time(natalie_schedule, william_schedule, meeting_duration))