from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, day, additional_constraints=None):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
        participants (dict): A dictionary where the keys are the participant names and the values are lists of tuples representing their busy times.
        meeting_duration (int): The duration of the meeting in minutes.
        work_hours (tuple): A tuple representing the start and end times of the work hours.
        day (str): The day of the week.
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

    # Iterate over the possible meeting times
    for i in range(int(work_hours_in_minutes - meeting_duration + 1)):
        # Calculate the current time
        current_time = start_time + timedelta(minutes=i)

        # Check if the current time works for all participants
        works_for_all = True
        for participant, busy_times in participants.items():
            for busy_time in busy_times:
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
                if constraint == "before 11:00":
                    if current_time >= datetime.strptime("11:00", "%H:%M"):
                        works_for_all = False
                        break

        # If the current time works for all participants and satisfies additional constraints, propose it
        if works_for_all:
            proposed_time = current_time.strftime("%H:%M") + ":" + (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
            break

    return proposed_time, day


# Example usage
participants = {
    "Deborah": [],
    "Albert": [("9:00", "10:00"), ("10:30", "12:00"), ("15:00", "16:30")]
}
meeting_duration = 30
work_hours = ("9:00", "17:00")
day = "Monday"
additional_constraints = {
    "Albert": "before 11:00"
}

proposed_time, day = find_meeting_time(participants, meeting_duration, work_hours, day, additional_constraints)
print(f"Proposed meeting time: {proposed_time} on {day}")