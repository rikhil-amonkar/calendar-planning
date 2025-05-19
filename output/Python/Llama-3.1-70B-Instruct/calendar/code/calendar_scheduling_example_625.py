from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, days, additional_constraints=None):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
        participants (dict): A dictionary where the keys are the participant names and the values are dictionaries with day as key and list of tuples representing their busy times as value.
        meeting_duration (int): The duration of the meeting in minutes.
        work_hours (tuple): A tuple representing the start and end times of the work hours.
        days (list): A list of days to consider for the meeting.
        additional_constraints (dict): A dictionary where the keys are the participant names and the values are additional constraints.

    Returns:
        tuple: A tuple containing the proposed meeting time and the day of the week.
    """

    # Convert work hours to minutes
    start_time = datetime.strptime(work_hours[0], "%H:%M")
    end_time = datetime.strptime(work_hours[1], "%H:%M")
    work_hours_in_minutes = (end_time - start_time).total_seconds() / 60

    # Initialize the proposed meeting time
    proposed_time = None

    # Iterate over the possible meeting days
    for day in days:
        # Iterate over the possible meeting times
        for i in range(int(work_hours_in_minutes - meeting_duration + 1)):
            # Calculate the current time
            current_time = start_time + timedelta(minutes=i)

            # Check if the current time works for all participants
            works_for_all = True
            for participant, schedule in participants.items():
                for busy_time in schedule.get(day, []):
                    busy_start_time = datetime.strptime(busy_time[0], "%H:%M")
                    busy_end_time = datetime.strptime(busy_time[1], "%H:%M")
                    if (current_time >= busy_start_time and current_time < busy_end_time) or \
                       (current_time + timedelta(minutes=meeting_duration) > busy_start_time and current_time < busy_end_time):
                        works_for_all = False
                        break
                if not works_for_all:
                    break

            # Check if the current time satisfies additional constraints
            if additional_constraints:
                for participant, constraint in additional_constraints.items():
                    if constraint == "avoid Monday":
                        if day == "Monday":
                            works_for_all = False
                            break
                    elif constraint == "Tuesday before 14:30":
                        if day == "Tuesday" and current_time >= datetime.strptime("14:30", "%H:%M"):
                            works_for_all = False
                            break

            # If the current time works for all participants and satisfies additional constraints, propose it
            if works_for_all:
                proposed_time = current_time.strftime("%H:%M") + ":" + (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
                proposed_day = day
                break

        if proposed_time:
            break

    return proposed_time, proposed_day


# Example usage
participants = {
    "Jeffrey": {"Monday": [], "Tuesday": []},
    "Harold": {"Monday": [("9:00", "10:00"), ("10:30", "17:00")], "Tuesday": [("9:00", "9:30"), ("10:30", "11:30"), ("12:30", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")]}
}
meeting_duration = 30
work_hours = ("9:00", "17:00")
days = ["Monday", "Tuesday"]
additional_constraints = {
    "Harold": "avoid Monday, Tuesday before 14:30"
}

proposed_time, day = find_meeting_time(participants, meeting_duration, work_hours, days, additional_constraints)
print(f"Proposed meeting time: {proposed_time} on {day}")