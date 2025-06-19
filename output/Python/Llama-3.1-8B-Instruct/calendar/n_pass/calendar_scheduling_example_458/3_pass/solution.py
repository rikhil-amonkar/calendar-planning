from datetime import datetime, timedelta

def find_meeting_time(participants, start_time, end_time, meeting_duration, preferences=None):
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")

    # Initialize a list to store available time slots
    available_time_slots = []

    # Iterate over each participant's schedule
    for participant in participants:
        # Get the participant's name and schedule
        name, schedule = participant

        # Initialize a flag to indicate if the participant has any available time slots
        has_available_time_slots = False

        # Iterate over each time slot in the participant's schedule
        for time_slot in schedule:
            # Get the start and end times of the time slot
            start, end = time_slot

            # Convert start and end times to datetime objects
            start = datetime.strptime(f"{start.split('.')[0]}:{start.split('.')[0]}", "%H:%M")
            end = datetime.strptime(f"{end.split('.')[0]}:{end.split('.')[0]}", "%H:%M")

            # If the time slot is not a meeting, add it to the available time slots
            if start > end:
                available_time_slots.append((start, end))

            # If the time slot is a meeting, check if it conflicts with the meeting duration
            else:
                # Calculate the end time of the meeting
                meeting_end = min(end, start + timedelta(minutes=meeting_duration*60))

                # Check if the meeting conflicts with the time slot
                if start <= end and end <= meeting_end:
                    # If the meeting conflicts, skip this time slot
                    continue

                # If the meeting does not conflict, add the time slot to the available time slots
                available_time_slots.append((start, end))
                has_available_time_slots = True

        # If the participant has no available time slots, return None
        if not has_available_time_slots:
            return None

    # Sort the available time slots by start time
    available_time_slots.sort(key=lambda x: x[0])

    # Initialize a variable to store the proposed meeting time
    proposed_meeting_time = None

    # Iterate over each available time slot
    for start, end in available_time_slots:
        # Check if the time slot meets the meeting duration and any preferences
        if (end - start).total_seconds() >= meeting_duration * 60 and (preferences is None or (start >= datetime.strptime(f"{14}:{14}", "%H:%M") and start < datetime.strptime(f"{17}:{17}", "%H:%M"))):
            # If the time slot meets the requirements, propose it as the meeting time
            proposed_meeting_time = (start, start + timedelta(minutes=meeting_duration*60))
            break

    # If no proposed meeting time is found, return None
    if proposed_meeting_time is None:
        return None

    # Format the proposed meeting time as a string
    meeting_time_str = f"{proposed_meeting_time[0].hour:02d}:{proposed_meeting_time[0].minute:02d}-{proposed_meeting_time[1].hour:02d}:{proposed_meeting_time[1].minute:02d}"

    # Get the day of the week
    day_of_week = start_time.date().strftime("%A")

    # Return the proposed meeting time and day of the week
    return f"{day_of_week} - {meeting_time_str}"

# Define the participants' schedules
participants = [
    ("Wayne", [(9, 17)]),
    ("Melissa", [(10, 11), (12, 14), (15, 15.5)]),
    ("Catherine", [(9, 17)]),
    ("Gregory", [(12, 12.5), (15, 15.5)]),
    ("Victoria", [(9, 9.5), (10, 11), (13, 14), (14, 15), (15, 16)]),
    ("Thomas", [(10, 12), (12, 12.5), (14, 16)]),
    ("Jennifer", [(9, 9.5), (10, 10.5), (11, 13), (13, 14), (15, 15.5), (16, 17)])
]

# Define the start and end times, meeting duration, and preferences
start_time = "09:00"
end_time = "17:00"
meeting_duration = 0.5  # 30 minutes
preferences = {"Wayne": (14, 17)}

# Find the proposed meeting time
proposed_meeting_time = find_meeting_time(participants, start_time, end_time, meeting_duration, preferences)

# Print the proposed meeting time and day of the week
print(proposed_meeting_time)