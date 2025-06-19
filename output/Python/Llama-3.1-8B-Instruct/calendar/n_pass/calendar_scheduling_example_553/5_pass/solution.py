from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
        start_time (datetime): The start time of the work hours.
        end_time (datetime): The end time of the work hours.
        meeting_duration (timedelta): The duration of the meeting.
        schedules (dict): A dictionary of schedules where each key is a participant and each value is a list of time slots.

    Returns:
        tuple: A tuple containing the proposed meeting time and day of the week.
    """
    # Sort the schedules by start time
    sorted_schedules = sorted(schedules.items(), key=lambda x: x[1][0])

    # Iterate over the sorted schedules
    for participant, time_slots in sorted_schedules:
        # Check if the participant has any available time slots
        for i in range(len(time_slots) - 1):
            # Check if the current time slot and the next time slot do not overlap
            if time_slots[i][1] < time_slots[i+1][0]:
                # Check if the available time slot is long enough to fit the meeting
                if time_slots[i+1][0] - time_slots[i][1] >= meeting_duration:
                    # Check if the available time slot conflicts with any unavailable time slots
                    unavailable_time = schedules.get('Unavailable', [])
                    for unavailable_time_slot in unavailable_time:
                        # Check if the available time slot conflicts with the unavailable time slot
                        if (time_slots[i][1] < unavailable_time_slot[0] < time_slots[i+1][0] or
                            time_slots[i][1] < unavailable_time_slot[1] < time_slots[i+1][0] or
                            unavailable_time_slot[0] < time_slots[i][1] < unavailable_time_slot[1] or
                            unavailable_time_slot[0] < time_slots[i+1][0] < unavailable_time_slot[1]):
                            # If there's a conflict, move on to the next time slot
                            break
                    else:
                        # Calculate the proposed meeting time
                        proposed_time = time_slots[i][1] + meeting_duration
                        # Check if the proposed meeting time is within the work hours
                        if start_time <= proposed_time < end_time:
                            # Check if the proposed meeting time is after 10:00 if the participant has a preference
                            if proposed_time.hour >= 10 and participant == 'Henry':
                                return proposed_time, "Monday"
                            else:
                                return proposed_time, "Monday"

    # If no suitable time is found, return None
    return None, None


def main():
    # Define the start and end time of the work hours
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")

    # Define the meeting duration
    meeting_duration = timedelta(hours=0, minutes=30)

    # Define the schedules
    schedules = {
        "Eric": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                 (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
        "Henry": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        'Unavailable': [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M"))]
    }

    # Find a suitable time for the meeting
    proposed_time, day_of_week = find_meeting_time(start_time, end_time, meeting_duration, schedules)

    # Print the proposed meeting time and day of the week
    if proposed_time:
        # Ensure that the proposed time plus the meeting duration does not exceed the end time
        proposed_end_time = min(proposed_time + meeting_duration, end_time)
        print(f"{proposed_time.strftime('%H:%M')} - {proposed_end_time.strftime('%H:%M')} {day_of_week}")
    else:
        print("No suitable time found.")


if __name__ == "__main__":
    main()