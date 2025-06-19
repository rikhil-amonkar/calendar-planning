from datetime import datetime, timedelta

def schedule_meeting(patricia_schedule, jesse_schedule, meeting_duration):
    # Define work hours
    start_hour = 9
    end_hour = 17

    # Define days of the week
    days = ["Monday", "Tuesday"]

    # Find available time slots for Patricia
    patricia_available = []
    for day in days:
        if day == "Monday":
            for hour in range(start_hour, end_hour):
                if not any(start <= hour < end for start, end in patricia_schedule[day]):
                    patricia_available.append((day, hour, hour + 1))
        elif day == "Tuesday":
            for hour in range(start_hour, end_hour):
                if not any(start <= hour < end for start, end in patricia_schedule[day]):
                    patricia_available.append((day, hour, hour + 1))

    # Find available time slots for Jesse
    jesse_available = []
    for day in days:
        if day == "Monday":
            for hour in range(start_hour, end_hour):
                if not any(start <= hour < end for start, end in jesse_schedule[day]):
                    jesse_available.append((day, hour, hour + 1))
        elif day == "Tuesday":
            for hour in range(start_hour, end_hour):
                if not any(start <= hour < end for start, end in jesse_schedule[day]):
                    jesse_available.append((day, hour, hour + 1))

    # Find common available time slots for Patricia and Jesse
    common_available = [slot for slot in patricia_available if slot in jesse_available]

    # Check if there are any common available time slots
    if common_available:
        # Find the time slot that is closest to the start of the day
        closest_slot = min(common_available, key=lambda x: (datetime.strptime(x[0], "%A"), x[1]))

        # Check if the meeting duration fits in the time slot
        if closest_slot[2] - closest_slot[1] >= meeting_duration:
            # Calculate the end time of the meeting
            end_time = closest_slot[1] + meeting_duration

            # Format the time range
            start_time = f"{closest_slot[1]:02d}:00"
            end_time = f"{end_time:02d}:00"

            # Format the day of the week
            day = closest_slot[0]

            # Output the result
            print(f"{start_time}:{end_time} {day}")
        else:
            print("No available time slot can accommodate the meeting duration.")
    else:
        print("No available time slot for both participants.")

# Define schedules
patricia_schedule = {
    "Monday": [(10, 10.5), (11.5, 12), (13, 13.5), (14.5, 15.5), (16, 16.5)],
    "Tuesday": [(10, 10.5), (11, 12), (14, 16), (16.5, 17)]
}

jesse_schedule = {
    "Monday": [(9, 17)],
    "Tuesday": [(11, 11.5), (12, 12.5), (13, 14), (14.5, 15), (15.5, 17)]
}

meeting_duration = 1  # in hours

schedule_meeting(patricia_schedule, jesse_schedule, meeting_duration)