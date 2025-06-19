from datetime import datetime, timedelta

def find_meeting_time(stephanie_schedule, betty_schedule, meeting_duration, preferred_days):
    # Sort the schedules by start time
    stephanie_schedule.sort(key=lambda x: x[0])
    betty_schedule.sort(key=lambda x: x[0])

    # Iterate over the preferred days
    for day in preferred_days:
        # Convert day to weekday name
        day_name = datetime.strptime(str(day), "%w").strftime("%A")

        # Initialize the end time for the meeting
        end_time = datetime.strptime(f"{day_name} 09:00", "%A %H:%M")

        # Find a time slot that works for both Stephanie and Betty
        for start_time in stephanie_schedule:
            if start_time[0].weekday() == day and start_time[1].weekday() == day:
                for betty_time in betty_schedule:
                    if betty_time[0].weekday() == day and betty_time[1].weekday() == day:
                        # Check if the time slot is available for both
                        if start_time[0] < betty_time[1] and end_time > start_time[0] and end_time < betty_time[1]:
                            # Check if the meeting duration fits in the time slot
                            if end_time - start_time[0] >= timedelta(hours=meeting_duration):
                                # Calculate the proposed meeting time
                                proposed_time = (start_time[0] + timedelta(hours=meeting_duration)).strftime("%H:%M") + ":" + (start_time[0] + timedelta(hours=meeting_duration) + timedelta(minutes=30)).strftime("%H:%M") + " " + day_name
                                return proposed_time

        # If no time slot is found, increment the end time and try again
        end_time += timedelta(hours=1)

    # If no time slot is found, return a message
    return "No suitable time found"

# Define the schedules for Stephanie and Betty
stephanie_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 10:00", "%A %H:%M")),
    (datetime.strptime("Monday 10:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 12:00", "%A %H:%M")),
    (datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 14:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 12:00", "%A %H:%M"), datetime.strptime("Tuesday 13:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 09:00", "%A %H:%M"), datetime.strptime("Wednesday 10:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 13:00", "%A %H:%M"), datetime.strptime("Wednesday 14:00", "%A %H:%M"))
]

betty_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 10:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:00", "%A %H:%M"), datetime.strptime("Monday 11:30", "%A %H:%M")),
    (datetime.strptime("Monday 14:30", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Monday 15:30", "%A %H:%M"), datetime.strptime("Monday 16:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 09:00", "%A %H:%M"), datetime.strptime("Tuesday 09:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 11:30", "%A %H:%M"), datetime.strptime("Tuesday 12:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 12:30", "%A %H:%M"), datetime.strptime("Tuesday 14:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 15:30", "%A %H:%M"), datetime.strptime("Tuesday 16:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 10:00", "%A %H:%M"), datetime.strptime("Wednesday 11:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 12:00", "%A %H:%M"), datetime.strptime("Wednesday 14:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 14:30", "%A %H:%M"), datetime.strptime("Wednesday 17:00", "%A %H:%M"))
]

# Define the meeting duration and preferred days
meeting_duration = 1
preferred_days = [0, 1, 2]  # Monday, Tuesday, Wednesday

# Find the proposed meeting time
proposed_time = find_meeting_time(stephanie_schedule, betty_schedule, meeting_duration, preferred_days)

# Print the proposed meeting time
print(f"Proposed meeting time: {proposed_time}")