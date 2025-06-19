from datetime import datetime, timedelta

def schedule_meeting(robert_schedule, ralph_schedule, meeting_duration, day, preference=None):
    """
    Schedule a meeting between Robert and Ralph.

    Args:
    - robert_schedule (dict): Robert's schedule.
    - ralph_schedule (dict): Ralph's schedule.
    - meeting_duration (int): The duration of the meeting in minutes.
    - day (str): The day of the week (Monday, Tuesday, Wednesday).
    - preference (str, optional): Robert's preference for the day. Defaults to None.

    Returns:
    - str: A proposed time and day for the meeting in the format HH:MM-HH:MM, Day of the week.
    """
    # Filter the schedules for the given day
    robert_day_schedule = robert_schedule.get(day, {})
    ralph_day_schedule = ralph_schedule.get(day, {})

    # Sort the time ranges for both participants
    robert_times = sorted(robert_day_schedule.items())
    ralph_times = sorted(ralph_day_schedule.items())

    # Initialize the earliest available time for the meeting
    earliest_robert_time = None
    earliest_ralph_time = None

    # Iterate over the time ranges for both participants
    for start, end in robert_times:
        start_time = datetime.strptime(start, '%H:%M')
        end_time = datetime.strptime(end, '%H:%M')
        for start_r, end_r in ralph_times:
            start_r_time = datetime.strptime(start_r, '%H:%M')
            end_r_time = datetime.strptime(end_r, '%H:%M')
            # Check if the meeting can be scheduled within the time range
            if (start_time < start_r_time + timedelta(minutes=meeting_duration) and
                (end_time + timedelta(minutes=meeting_duration)) > start_r_time):
                # Check for conflicts with unavailable time slots
                for unavailable_start, unavailable_end in ralph_day_schedule.items():
                    unavailable_start_time = datetime.strptime(unavailable_start, '%H:%M')
                    unavailable_end_time = datetime.strptime(unavailable_end, '%H:%M')
                    # Check if the unavailable time slot conflicts with the meeting time range
                    if (start_time < unavailable_end_time and
                        (end_time + timedelta(minutes=meeting_duration)) > unavailable_start_time):
                        # If a conflict is found, skip this time range
                        continue
                # Check if the time range conflicts with unavailable time slots in Robert's schedule
                for robert_unavailable_start, robert_unavailable_end in robert_day_schedule.items():
                    robert_unavailable_start_time = datetime.strptime(robert_unavailable_start, '%H:%M')
                    robert_unavailable_end_time = datetime.strptime(robert_unavailable_end, '%H:%M')
                    # Check if the time range conflicts with the unavailable time slot
                    if (start_r_time < robert_unavailable_end_time and
                        (end_r_time + timedelta(minutes=meeting_duration)) > robert_unavailable_start_time):
                        # If a conflict is found, skip this time range
                        continue
                # Update the earliest available time for the meeting
                if earliest_robert_time is None or start_time < earliest_robert_time:
                    earliest_robert_time = start_time
                if earliest_ralph_time is None or start_r_time < earliest_ralph_time:
                    earliest_ralph_time = start_r_time

    # Check if a meeting can be scheduled within the time range
    if earliest_robert_time is not None and earliest_ralph_time is not None:
        # Calculate the end time of the meeting
        end_time = earliest_robert_time + timedelta(minutes=meeting_duration)

        # Return the proposed time and day for the meeting
        return f"{earliest_robert_time.strftime('%H:%M')}-{end_time.strftime('%H:%M')}, {day}"
    else:
        # Return a message indicating that a meeting cannot be scheduled
        return "No available time for the meeting."


def main():
    # Define the schedules for Robert and Ralph
    robert_schedule = {
        "Monday": {
            "11:00": "11:30",
            "14:00": "14:30",
            "15:30": "16:00"
        },
        "Tuesday": {
            "10:30": "11:00",
            "15:00": "15:30"
        },
        "Wednesday": {
            "10:00": "11:00",
            "11:30": "12:00",
            "12:30": "13:00",
            "13:30": "14:00",
            "15:00": "15:30",
            "16:00": "16:30"
        }
    }

    ralph_schedule = {
        "Monday": {
            "10:00": "13:30",
            "14:00": "14:30",
            "15:00": "17:00"
        },
        "Tuesday": {
            "9:00": "9:30",
            "10:00": "10:30",
            "11:00": "11:30",
            "12:00": "13:00",
            "14:00": "15:30",
            "16:00": "17:00"
        },
        "Wednesday": {
            "10:30": "11:00",
            "11:30": "12:00",
            "13:00": "14:30",
            "16:30": "17:00",
            "10:00": "11:00"  # Unavailable time slot
        }
    }

    # Define the meeting duration
    meeting_duration = 30  # minutes

    # Define the day of the week
    day = "Wednesday"

    # Schedule the meeting
    proposed_time = schedule_meeting(robert_schedule, ralph_schedule, meeting_duration, day)

    # Print the proposed time and day for the meeting
    print(proposed_time)


if __name__ == "__main__":
    main()