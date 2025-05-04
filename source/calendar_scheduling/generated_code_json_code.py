from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, preferences):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (dict): A dictionary of participants with their schedules.
    meeting_duration (int): The duration of the meeting in minutes.
    work_hours (tuple): A tuple representing the start and end of work hours.
    preferences (dict): A dictionary of participants with their time preferences.

    Returns:
    str: A proposed time for the meeting in the format HH:MM-HH:MM.
    """
    # Convert work hours to datetime objects
    start_time = datetime.strptime(work_hours[0], "%H:%M")
    end_time = datetime.strptime(work_hours[1], "%H:%M")

    # Initialize the current time to the start of work hours
    current_time = start_time

    # Loop through each minute of the work hours
    while current_time < end_time:
        # Check if the current time is available for all participants
        available = True
        for participant, schedule in participants.items():
            # Check if the participant is busy at the current time
            for start, end in schedule:
                start_time = datetime.strptime(start, "%H:%M")
                end_time = datetime.strptime(end, "%H:%M")
                if current_time >= start_time and current_time < end_time:
                    available = False
                    break
            # Check if the participant has a time preference
            if participant in preferences:
                preference_time = datetime.strptime(preferences[participant], "%H:%M")
                if current_time < preference_time:
                    available = False
                    break
        # If the current time is available for all participants, propose it as the meeting time
        if available:
            # Calculate the end time of the meeting
            meeting_end_time = current_time + timedelta(minutes=meeting_duration)
            # Format the proposed meeting time
            proposed_time = f"{current_time.strftime('%H:%M')}-{meeting_end_time.strftime('%H:%M')}"
            return proposed_time
        # Move to the next minute
        current_time += timedelta(minutes=1)

def main():
    # Define the participants' schedules
    participants = {
        "Shirley": [("10:30", "11:00"), ("12:00", "12:30")],
        "Jacob": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:30", "15:00")],
        "Stephen": [("11:30", "12:00"), ("12:30", "13:00")],
        "Margaret": [("9:00", "9:30"), ("10:30", "12:30"), ("13:00", "13:30"), ("15:00", "15:30"), ("16:30", "17:00")],
        "Mason": [("9:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")],
    }

    # Define the meeting duration
    meeting_duration = 30

    # Define the work hours
    work_hours = ("9:00", "17:00")

    # Define the time preferences
    preferences = {
        "Margaret": "14:30",
    }

    # Find a proposed time for the meeting
    proposed_time = find_meeting_time(participants, meeting_duration, work_hours, preferences)

    # Print the proposed meeting time
    print(proposed_time)

if __name__ == "__main__":
    main()