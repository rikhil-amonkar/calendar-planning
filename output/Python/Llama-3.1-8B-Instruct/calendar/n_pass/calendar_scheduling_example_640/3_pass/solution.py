from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    schedules (dict): A dictionary where keys are participant names and values are lists of busy times.
    meeting_duration (int): The duration of the meeting in minutes.

    Returns:
    tuple: A tuple containing the proposed time and day of the week.
    """
    # Define the work hours and days
    work_hours = (9, 17)
    work_days = ['Monday', 'Tuesday']

    # Initialize the proposed time and day
    proposed_time = None
    proposed_day = None

    # Iterate over each day
    for day in work_days:
        # Initialize the current time
        current_time = work_hours[0] * 60  # Convert hours to minutes

        # Iterate until we find a time that works for everyone
        while current_time < work_hours[1] * 60:
            # Assume this time works for everyone
            works_for_everyone = True

            # Check each participant's schedule
            for participant, busy_times in schedules.items():
                # Check if the current time is busy for this participant
                for busy_time in busy_times:
                    if busy_time[0] <= current_time < busy_time[1]:
                        # This time is busy for this participant
                        works_for_everyone = False
                        break

                # If this time doesn't work for this participant, break
                if not works_for_everyone:
                    break

            # If this time works for everyone, update the proposed time and day
            if works_for_everyone:
                start_time = datetime.strptime(f'{day} {current_time // 60:02d}:{current_time % 60:02d}', '%A %H:%M').time()
                end_time = datetime.strptime(f'{day} {(current_time + meeting_duration) // 60:02d}:{(current_time + meeting_duration) % 60:02d}', '%A %H:%M').time()
                proposed_time = (start_time, end_time)
                proposed_day = day
                break

            # Move to the next time slot
            current_time += 30  # Increment by 30 minutes

        # If we found a proposed time and day, break
        if proposed_time:
            break

    # Check if a meeting can be scheduled
    if proposed_time:
        # Check each participant's schedule
        for participant, busy_times in schedules.items():
            # Check if the proposed time is busy for this participant
            for busy_time in busy_times:
                if busy_time[0] <= proposed_time[0].hour * 60 + proposed_time[0].minute < busy_time[1] and busy_time[0] <= proposed_time[1].hour * 60 + proposed_time[1].minute < busy_time[1]:
                    # This time is busy for this participant
                    proposed_time = None
                    break

        # If the proposed time is still valid, return it
        if proposed_time:
            return proposed_time, proposed_day
        else:
            return None, None
    else:
        return None, None


# Define the schedules and meeting duration
schedules = {
    'Bobby': [(14 * 60 + 30, 15 * 60), (9 * 60 + 0, 11 * 60 + 30), (12 * 60 + 0, 12 * 60 + 30), (13 * 60 + 0, 15 * 60),
              (15 * 60 + 30, 17 * 60)],
    'Michael': [(9 * 60 + 0, 10 * 60), (10 * 60 + 30, 13 * 60 + 30), (14 * 60 + 0, 15 * 60), (15 * 60 + 30, 17 * 60),
                (9 * 60 + 0, 10 * 60 + 30), (11 * 60 + 0, 11 * 60 + 30), (12 * 60 + 0, 14 * 60), (15 * 60 + 0, 16 * 60),
                (16 * 60 + 30, 17 * 60)]
}
meeting_duration = 30  # 30 minutes

# Find the proposed time and day
proposed_time, proposed_day = find_meeting_time(schedules, meeting_duration)

# Print the proposed time and day
if proposed_time:
    print(f'{proposed_time[0].strftime("%H:%M")}-{proposed_time[1].strftime("%H:%M")}, {proposed_day}')
else:
    print("No proposed time and day found.")