from datetime import datetime, timedelta

def find_meeting_time(megan_schedule, daniel_schedule, meeting_duration):
    # Define the work hours and days
    work_hours = [(9, 17), (13, 17)]
    work_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Find the first available time slot for both Megan and Daniel
    for day in work_days:
        for start_hour in work_hours:
            for end_hour in work_hours:
                if (start_hour[0] == 9 and end_hour[0] == 17) or (start_hour[0] == 13 and end_hour[0] == 17):
                    time_slot = (start_hour[0], end_hour[0])
                    if day in work_days:
                        # Check if the time slot is available in Megan's schedule
                        if day in megan_schedule and time_slot not in megan_schedule[day]:
                            # Check if the time slot is available in Daniel's schedule
                            if day in daniel_schedule and time_slot not in daniel_schedule[day]:
                                # Check if the time slot is long enough to accommodate the meeting duration
                                if end_hour[0] - start_hour[0] >= meeting_duration:
                                    return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'

    # If no available time slot is found, return a message
    return 'No available time slot found'

# Define the schedules for Megan and Daniel
megan_schedule = {
    'Monday': [(13, 13.5), (14, 15.5)],
    'Tuesday': [(9, 9.5), (12, 12.5), (16, 17)],
    'Wednesday': [(9.5, 10), (10.5, 11.5), (12.5, 14), (16, 16.5)],
    'Thursday': [(13.5, 14.5), (15, 15.5)]
}

daniel_schedule = {
    'Monday': [(10, 11.5), (12.5, 15), (12.5, 15)],
    'Tuesday': [(9, 10), (10.5, 17), (9, 10), (10.5, 17)],
    'Wednesday': [(9, 10), (10.5, 11.5), (12, 17), (9, 10), (10.5, 11.5), (12, 17)],
    'Thursday': [(9, 12), (12.5, 14.5), (15, 15.5), (9, 12), (12.5, 14.5), (15, 15.5)]
}

# Define the meeting duration
meeting_duration = 1

# Find the meeting time
meeting_time = find_meeting_time(megan_schedule, daniel_schedule, meeting_duration)
print(meeting_time)