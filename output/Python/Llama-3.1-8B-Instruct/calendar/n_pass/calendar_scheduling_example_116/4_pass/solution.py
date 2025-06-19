from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferences=None):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (dict): A dictionary where the keys are the participant names and the values are their schedules.
    meeting_duration (int): The duration of the meeting in minutes.
    preferences (dict): A dictionary where the keys are the participant names and the values are their preferences.

    Returns:
    str: A string representing the proposed meeting time in the format HH:MM-HH:MM, day of the week.
    """
    # Convert meeting duration from minutes to hours and minutes
    meeting_duration_hours = meeting_duration // 60
    meeting_duration_minutes = meeting_duration % 60

    # Initialize a list to store the available time slots for each participant
    available_time_slots = []

    # Iterate over the participants and their schedules
    for participant, schedule in participants.items():
        # Initialize a list to store the available time slots for the current participant
        participant_available_time_slots = []

        # Iterate over the time slots in the schedule
        for start_time, end_time in schedule:
            # Convert the time slots to datetime objects
            start_time = datetime.strptime(f"{start_time}:00", "%H:%M")
            end_time = datetime.strptime(f"{end_time}:00", "%H:%M")

            # Calculate the available time slots for the current participant
            if start_time.hour > 8 and start_time.hour < 17:
                if start_time.minute == 0:
                    start_time = start_time.replace(minute=30)
                if end_time.minute == 0:
                    end_time = end_time.replace(minute=30)

                # If the participant has a preference, check if it conflicts with the available time slots
                if preferences and participant in preferences:
                    preference = preferences[participant]
                    if preference and start_time.time() < preference and end_time.time() > preference:
                        start_time = datetime.combine(datetime.today(), preference)
                        end_time = start_time + timedelta(hours=1)

                # Calculate the available time slots
                for i in range(int((end_time - start_time).total_seconds() / 3600)):
                    time_slot_start = start_time + timedelta(hours=i)
                    time_slot_end = start_time + timedelta(hours=i + 1)
                    if time_slot_start.hour > 8 and time_slot_start.hour < 17:
                        participant_available_time_slots.append((time_slot_start, time_slot_end))

        # Add the available time slots for the current participant to the list of all available time slots
        available_time_slots.extend(participant_available_time_slots)

    # Sort the available time slots by start time
    available_time_slots.sort(key=lambda x: x[0])

    # Initialize a variable to store the proposed meeting time
    proposed_meeting_time = None

    # Iterate over the available time slots
    for i in range(len(available_time_slots) - 1):
        # Calculate the end time of the current time slot
        end_time = available_time_slots[i][1]

        # Calculate the start time of the next time slot
        next_start_time = available_time_slots[i + 1][0]

        # Check if the current time slot is long enough for the meeting
        if end_time - available_time_slots[i][0] >= timedelta(hours=meeting_duration_hours, minutes=meeting_duration_minutes):
            # Check if the next time slot is long enough for the meeting
            if next_start_time - end_time >= timedelta(hours=meeting_duration_hours, minutes=meeting_duration_minutes):
                # Check if the current time slot conflicts with any other participant's schedule
                conflicts = False
                for j in range(len(available_time_slots)):
                    if available_time_slots[j][0] < end_time and available_time_slots[j][1] > end_time:
                        conflicts = True
                        break

                # If there are no conflicts, propose the current time slot as the meeting time
                if not conflicts:
                    proposed_meeting_time = (available_time_slots[i][0].strftime("%H:%M"), available_time_slots[i][1].strftime("%H:%M"))
                    break

    # Return the proposed meeting time and the day of the week
    if proposed_meeting_time:
        day_of_week = datetime.strptime("2024-01-01", "%Y-%m-%d").strftime("%A")
        return f"{day_of_week}, {proposed_meeting_time[0]}-{proposed_meeting_time[1]}"
    else:
        return "No available time slot found"

# Define the participants' schedules and preferences
participants = {
    "Adam": [(9, 17), (14, 15)],
    "John": [(13, 13), (14, 14), (15, 16), (16, 17)],
    "Stephanie": [(9, 10), (10, 11), (11, 16), (16, 17)],
    "Anna": [(9, 10), (12, 12), (13, 15), (16, 17)]
}

preferences = {
    "Anna": datetime.strptime("14:30:00", "%H:%M:%S").time()
}

# Define the meeting duration
meeting_duration = 30

# Find the proposed meeting time
proposed_meeting_time = find_meeting_time(participants, meeting_duration, preferences)

# Print the proposed meeting time
print(proposed_meeting_time)