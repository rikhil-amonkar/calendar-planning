from datetime import datetime, timedelta

def check_conflicts(natalie_schedule, william_schedule, unavailable_slots, start_time, end_time, day):
    # Check if time is available for both participants and not in unavailable slots
    for hour in range(start_time[0], end_time[0] + 1):
        for minute in range(start_time[1], end_time[1] + 1):
            if (hour, minute) in natalie_schedule.get(day, []) or \
               (hour, minute) in william_schedule.get(day, []) or \
               (hour, minute) in unavailable_slots.get(day, []):
                return True

    return False


def find_meeting_time(natalie_schedule, william_schedule, unavailable_slots, meeting_duration):
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
            # Check if there is enough time for the meeting
            if hour + meeting_duration // 60 <= end_hour:
                end_time = (hour + meeting_duration // 60, 0)
                if minute + meeting_duration % 60 <= 59:
                    end_time = (hour + meeting_duration // 60, minute + meeting_duration % 60)
                # Check for conflicts
                if not check_conflicts(natalie_schedule, william_schedule, unavailable_slots, (hour, minute), end_time, day):
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

unavailable_slots = {
    "Monday": [(9, 0), (9, 30), (10, 0), (10, 30), (12, 0), (12, 30), (14, 0), (14, 30), (15, 0), (16, 30)],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": []
}

meeting_duration = 60

# Find the meeting time
print(find_meeting_time(natalie_schedule, william_schedule, unavailable_slots, meeting_duration))