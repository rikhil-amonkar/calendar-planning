from datetime import datetime, timedelta

def find_meeting_time(megan_schedule, daniel_schedule, meeting_duration):
    # Define the work hours and days
    work_hours = [(9, 17), (13, 17)]
    work_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Find the first available time slot for Megan
    for day in work_days:
        for start_hour in work_hours:
            for end_hour in work_hours:
                if (start_hour[0] == 9 and end_hour[0] == 17) or (start_hour[0] == 13 and end_hour[0] == 17):
                    time_slot = (start_hour[0], end_hour[0])
                    if day in work_days:
                        if day == 'Monday':
                            if not (13 <= time_slot[0] <= 13.5 or 14 <= time_slot[0] <= 15.5):
                                if not (13 <= time_slot[1] <= 13.5 or 14 <= time_slot[1] <= 15.5):
                                    if time_slot not in megan_schedule['Monday']:
                                        return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'
                        elif day == 'Tuesday':
                            if not (9 <= time_slot[0] <= 9.5 or 12 <= time_slot[0] <= 12.5 or 16 <= time_slot[0] <= 17):
                                if not (9 <= time_slot[1] <= 9.5 or 12 <= time_slot[1] <= 12.5 or 16 <= time_slot[1] <= 17):
                                    if time_slot not in megan_schedule['Tuesday']:
                                        return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'
                        elif day == 'Wednesday':
                            if not (9.5 <= time_slot[0] <= 10 or 10.5 <= time_slot[0] <= 11.5 or 12.5 <= time_slot[0] <= 14 or 16 <= time_slot[0] <= 16.5):
                                if not (9.5 <= time_slot[1] <= 10 or 10.5 <= time_slot[1] <= 11.5 or 12.5 <= time_slot[1] <= 14 or 16 <= time_slot[1] <= 16.5):
                                    if time_slot not in megan_schedule['Wednesday']:
                                        return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'
                        elif day == 'Thursday':
                            if not (13.5 <= time_slot[0] <= 14.5 or 15 <= time_slot[0] <= 15.5):
                                if not (13.5 <= time_slot[1] <= 14.5 or 15 <= time_slot[1] <= 15.5):
                                    if time_slot not in megan_schedule['Thursday']:
                                        return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'

    # Find the first available time slot for Daniel
    for day in work_days:
        for start_hour in work_hours:
            for end_hour in work_hours:
                if (start_hour[0] == 9 and end_hour[0] == 17) or (start_hour[0] == 13 and end_hour[0] == 17):
                    time_slot = (start_hour[0], end_hour[0])
                    if day in work_days:
                        if day == 'Monday':
                            if not (10 <= time_slot[0] <= 11.5 or 12.5 <= time_slot[0] <= 15 or 12.5 <= time_slot[1] <= 15):
                                if time_slot not in daniel_schedule['Monday']:
                                    return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'
                        elif day == 'Tuesday':
                            if not (9 <= time_slot[0] <= 10 or 10.5 <= time_slot[0] <= 17 or 9 <= time_slot[1] <= 10 or 10.5 <= time_slot[1] <= 17):
                                if time_slot not in daniel_schedule['Tuesday']:
                                    return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'
                        elif day == 'Wednesday':
                            if not (9 <= time_slot[0] <= 10 or 10.5 <= time_slot[0] <= 11.5 or 12 <= time_slot[0] <= 17 or 9 <= time_slot[1] <= 10 or 10.5 <= time_slot[1] <= 11.5 or 12 <= time_slot[1] <= 17):
                                if time_slot not in daniel_schedule['Wednesday']:
                                    return f'{day}, {time_slot[0]:02d}:{time_slot[0]:02d} - {time_slot[1]:02d}:{time_slot[1]:02d}'
                        elif day == 'Thursday':
                            if not (9 <= time_slot[0] <= 12 or 12.5 <= time_slot[0] <= 14.5 or 15 <= time_slot[0] <= 15.5 or 9 <= time_slot[1] <= 12 or 12.5 <= time_slot[1] <= 14.5 or 15 <= time_slot[1] <= 15.5):
                                if time_slot not in daniel_schedule['Thursday']:
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