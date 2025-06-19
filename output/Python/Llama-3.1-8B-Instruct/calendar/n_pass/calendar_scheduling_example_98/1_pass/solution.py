from datetime import datetime, timedelta

def schedule_meeting(juan_schedule, marilyn_schedule, ronald_schedule, meeting_duration):
    # Sort the schedules by start time
    schedules = [juan_schedule, marilyn_schedule, ronald_schedule]
    schedules.sort(key=lambda x: x[0])

    # Initialize the proposed time
    proposed_time = None

    # Iterate over the possible meeting times
    for hour in range(9, 17):
        for minute in range(0, 60, meeting_duration):
            time = datetime(2024, 1, 1, hour, minute)

            # Check if the proposed time works for everyone
            if all(time + timedelta(minutes=meeting_duration) <= schedule[1] and time >= schedule[0] for schedule in schedules):
                proposed_time = (time.strftime("%H:%M"), (time + timedelta(minutes=meeting_duration)).strftime("%H:%M"))
                break

        if proposed_time:
            break

    # Return the proposed time and the day of the week
    day_of_week = datetime(2024, 1, 1).strftime("%A")
    return f"{proposed_time[0]} - {proposed_time[1]} on {day_of_week}"

# Define the existing schedules
juan_schedule = (datetime(2024, 1, 1, 9, 0), datetime(2024, 1, 1, 10, 30))
marilyn_schedule = (datetime(2024, 1, 1, 11, 0), datetime(2024, 1, 1, 11, 30))
ronald_schedule = (datetime(2024, 1, 1, 9, 0), datetime(2024, 1, 1, 10, 30))
juan_schedule = (juan_schedule[0], datetime(2024, 1, 1, 15, 30))
marilyn_schedule = (marilyn_schedule[0], datetime(2024, 1, 1, 12, 30))
ronald_schedule = (ronald_schedule[0], datetime(2024, 1, 1, 12, 0))
ronald_schedule = (ronald_schedule[0], datetime(2024, 1, 1, 12, 30))
ronald_schedule = (ronald_schedule[0], datetime(2024, 1, 1, 13, 0))
ronald_schedule = (ronald_schedule[0], datetime(2024, 1, 1, 13, 30))
ronald_schedule = (ronald_schedule[0], datetime(2024, 1, 1, 14, 0))
ronald_schedule = (ronald_schedule[0], datetime(2024, 1, 1, 16, 30))

# Define the meeting duration
meeting_duration = 30

# Print the proposed time
print(schedule_meeting(juan_schedule, marilyn_schedule, ronald_schedule, meeting_duration))