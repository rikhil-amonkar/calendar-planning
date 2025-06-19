from datetime import datetime, timedelta

def find_meeting_time(stephanie_schedule, betty_schedule, meeting_duration, preferred_days):
    # Sort the schedules by start time
    stephanie_schedule.sort(key=lambda x: x[0])
    betty_schedule.sort(key=lambda x: x[0])

    # Iterate over the preferred days
    for day in preferred_days:
        # Initialize the end time for the meeting
        end_time = datetime.strptime(f"{datetime.strptime(str(day), '%w').strftime('%A')} 09:00", '%A %H:%M')

        # Find a time slot that works for both Stephanie and Betty
        stephanie_index = 0
        while stephanie_index < len(stephanie_schedule) and stephanie_schedule[stephanie_index][0].weekday()!= day:
            stephanie_index += 1

        betty_index = 0
        while betty_index < len(betty_schedule) and betty_schedule[betty_index][0].weekday()!= day:
            betty_index += 1

        while stephanie_index < len(stephanie_schedule) and betty_index < len(betty_schedule):
            # Check if the time slot is available for both
            if (end_time >= stephanie_schedule[stephanie_index][0] and end_time <= stephanie_schedule[stephanie_index][1]) and \
               (end_time >= betty_schedule[betty_index][0] and end_time <= betty_schedule[betty_index][1]):
                # Check if the meeting duration fits in the time slot
                if end_time - stephanie_schedule[stephanie_index][0] >= timedelta(hours=meeting_duration) and \
                   betty_schedule[betty_index][1] - end_time >= timedelta(hours=meeting_duration):
                    # Calculate the proposed meeting time
                    proposed_time = (end_time + timedelta(hours=meeting_duration)).strftime('%H:%M') + ":" + \
                                    (end_time + timedelta(hours=meeting_duration) + timedelta(minutes=30)).strftime('%H:%M') + " " + \
                                    datetime.strptime(str(day), '%w').strftime('%A')
                    return proposed_time

            # Move to the next time slot
            if stephanie_schedule[stephanie_index][1] < betty_schedule[betty_index][1]:
                stephanie_index += 1
            else:
                betty_index += 1

            # If no time slot is found, increment the end time and try again
            end_time += timedelta(hours=1)

    # If no time slot is found, return a message
    return "No suitable time found"

# Define the schedules for Stephanie and Betty
stephanie_schedule = [
    (datetime.strptime("Monday 09:30", '%A %H:%M'), datetime.strptime("Monday 10:00", '%A %H:%M')),
    (datetime.strptime("Monday 10:30", '%A %H:%M'), datetime.strptime("Monday 11:00", '%A %H:%M')),
    (datetime.strptime("Monday 11:30", '%A %H:%M'), datetime.strptime("Monday 12:00", '%A %H:%M')),
    (datetime.strptime("Monday 14:00", '%A %H:%M'), datetime.strptime("Monday 14:30", '%A %H:%M')),
    (datetime.strptime("Tuesday 12:00", '%A %H:%M'), datetime.strptime("Tuesday 13:00", '%A %H:%M')),
    (datetime.strptime("Wednesday 09:00", '%A %H:%M'), datetime.strptime("Wednesday 10:00", '%A %H:%M')),
    (datetime.strptime("Wednesday 13:00", '%A %H:%M'), datetime.strptime("Wednesday 14:00", '%A %H:%M'))
]

betty_schedule = [
    (datetime.strptime("Monday 09:00", '%A %H:%M'), datetime.strptime("Monday 10:00", '%A %H:%M')),
    (datetime.strptime("Monday 11:00", '%A %H:%M'), datetime.strptime("Monday 11:30", '%A %H:%M')),
    (datetime.strptime("Monday 14:30", '%A %H:%M'), datetime.strptime("Monday 15:00", '%A %H:%M')),
    (datetime.strptime("Monday 15:30", '%A %H:%M'), datetime.strptime("Monday 16:00", '%A %H:%M')),
    (datetime.strptime("Tuesday 09:00", '%A %H:%M'), datetime.strptime("Tuesday 09:30", '%A %H:%M')),
    (datetime.strptime("Tuesday 11:30", '%A %H:%M'), datetime.strptime("Tuesday 12:00", '%A %H:%M')),
    (datetime.strptime("Tuesday 12:30", '%A %H:%M'), datetime.strptime("Tuesday 14:30", '%A %H:%M')),
    (datetime.strptime("Tuesday 15:30", '%A %H:%M'), datetime.struts.strptime("Tuesday 16:00", '%A %H:%M')),
    (datetime.strptime("Wednesday 10:00", '%A %H:%M'), datetime.strptime("Wednesday 11:30", '%A %H:%M')),
    (datetime.strptime("Wednesday 12:00", '%A %H:%M'), datetime.strptime("Wednesday 14:00", '%A %H:%M')),
    (datetime.strptime("Wednesday 14:30", '%A %H:%M'), datetime.strptime("Wednesday 17:00", '%A %H:%M'))
]

# Define the meeting duration and preferred days
meeting_duration = 1
preferred_days = [0, 1, 2]  # Monday, Tuesday, Wednesday

# Find the proposed meeting time
proposed_time = find_meeting_time(stephanie_schedule, betty_schedule, meeting_duration, preferred_days)

# Print the proposed meeting time
print(f"Proposed meeting time: {proposed_time}")