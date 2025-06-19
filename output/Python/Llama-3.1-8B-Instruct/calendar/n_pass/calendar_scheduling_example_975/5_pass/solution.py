from datetime import datetime, timedelta

def find_available_time(nicole_schedule, daniel_schedule):
    # Define the work hours and days
    work_hours = range(9, 18)
    work_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

    # Combine Nicole's and Daniel's schedules into a single list
    combined_schedule = nicole_schedule + daniel_schedule

    # Find the earliest available time for both participants
    for day in work_days:
        for hour in work_hours:
            start_time = datetime.combine(datetime.today(), datetime.min.time()) + timedelta(days=work_days.index(day), hours=hour)
            end_time = start_time + timedelta(hours=1)

            # Check if the time is available for both participants
            available = True
            for slot in combined_schedule:
                if start_time >= slot[0] and start_time < slot[1]:
                    # If the start time of the meeting is before the end time of the slot, 
                    # then the meeting duration is conflicting with the slot
                    available = False
                    break
                elif end_time > slot[0] and end_time <= slot[1]:
                    # If the end time of the meeting is after the start time of the slot, 
                    # then the meeting duration is conflicting with the slot
                    available = False
                    break
                elif start_time < slot[0] and end_time > slot[1]:
                    # If the start time of the meeting is before the start time of the slot and the end time of the meeting is after the end time of the slot, 
                    # then the meeting duration is conflicting with the slot
                    available = False
                    break

            if available:
                return f"{day}, {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}"

    return "No available time found"

# Define the schedules for Nicole and Daniel
nicole_schedule = [
    (datetime(2024, 7, 2, 16, 0), datetime(2024, 7, 2, 16, 30)),
    (datetime(2024, 7, 3, 15, 0), datetime(2024, 7, 3, 15, 30)),
    (datetime(2024, 7, 5, 12, 0), datetime(2024, 7, 5, 12, 30)),
    (datetime(2024, 7, 5, 15, 30), datetime(2024, 7, 5, 16, 0)),
]

daniel_schedule = [
    (datetime(2024, 7, 1, 9, 0), datetime(2024, 7, 1, 12, 30)),
    (datetime(2024, 7, 1, 13, 0), datetime(2024, 7, 1, 13, 30)),
    (datetime(2024, 7, 1, 14, 0), datetime(2024, 7, 1, 16, 30)),
    (datetime(2024, 7, 2, 9, 0), datetime(2024, 7, 2, 10, 30)),
    (datetime(2024, 7, 2, 11, 30), datetime(2024, 7, 2, 12, 30)),
    (datetime(2024, 7, 2, 13, 0), datetime(2024, 7, 2, 13, 30)),
    (datetime(2024, 7, 2, 15, 0), datetime(2024, 7, 2, 16, 0)),
    (datetime(2024, 7, 2, 16, 30), datetime(2024, 7, 2, 17, 0)),
    (datetime(2024, 7, 3, 9, 0), datetime(2024, 7, 3, 10, 0)),
    (datetime(2024, 7, 3, 11, 0), datetime(2024, 7, 3, 12, 30)),
    (datetime(2024, 7, 3, 13, 0), datetime(2024, 7, 3, 13, 30)),
    (datetime(2024, 7, 3, 14, 0), datetime(2024, 7, 3, 14, 30)),
    (datetime(2024, 7, 3, 16, 30), datetime(2024, 7, 3, 17, 0)),
    (datetime(2024, 7, 4, 11, 0), datetime(2024, 7, 4, 12, 0)),
    (datetime(2024, 7, 4, 13, 0), datetime(2024, 7, 4, 14, 0)),
    (datetime(2024, 7, 4, 15, 0), datetime(2024, 7, 4, 15, 30)),
    (datetime(2024, 7, 5, 10, 0), datetime(2024, 7, 5, 11, 0)),
    (datetime(2024, 7, 5, 11, 30), datetime(2024, 7, 5, 12, 0)),
    (datetime(2024, 7, 5, 12, 30), datetime(2024, 7, 5, 14, 30)),
    (datetime(2024, 7, 5, 15, 0), datetime(2024, 7, 5, 15, 30)),
    (datetime(2024, 7, 5, 16, 0), datetime(2024, 7, 5, 16, 30)),
]

print(find_available_time(nicole_schedule, daniel_schedule))