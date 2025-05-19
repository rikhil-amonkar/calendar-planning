def find_meeting_time():
    # Define the work hours
    work_hours = [(9, 17)]  # (start, end) in HH:MM format

    # Define the days in order: Monday, Tuesday, Wednesday, Thursday
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Betty's schedule
    betty_schedule = {
        'Monday': [(10, 10, 30), (13, 30, 14), (15, 0, 15, 30), (16, 0, 16, 30)],
        'Tuesday': [(9, 0, 9, 30), (11, 30, 12), (12, 30, 13), (13, 30, 14), (16, 30, 17)],
        'Wednesday': [(9, 30, 10), (13, 0, 13, 30), (14, 0, 14, 30)],
        'Thursday': [(9, 30, 10), (11, 30, 12), (14, 0, 14, 30), (15, 0, 15, 30), (16, 30, 17)]
    }

    # Scott's schedule
    scott_schedule = {
        'Monday': [(9, 30, 15), (15, 30, 16), (16, 30, 17)],
        'Tuesday': [(9, 0, 9, 30), (10, 0, 11), (11, 30, 12), (12, 30, 13, 30), (14, 0, 15)],
        'Wednesday': [(9, 30, 12, 30), (13, 0, 13, 30), (14, 0, 14, 30), (15, 0, 15, 30), (16, 0, 16, 30)],
        'Thursday': [(9, 0, 9, 30), (10, 0, 10, 30), (11, 0, 12), (12, 30, 13), (15, 0, 16), (16, 30, 17)]
    }

    # Function to convert minutes to HH:MM format
    def minutes_to_time(minutes):
        hours, mins = divmod(minutes, 60)
        return f"{hours:02d}:{mins:02d}"

    # Function to check if a time slot is free for a person
    def is_free(person, day, start, end):
        if day not in person:
            return False
        for time in person[day]:
            if start <= time[0] <= end:
                return False
        return True

    # Iterate through each day
    for day in days:
        if day == 'Monday' or day == 'Tuesday' or day == 'Wednesday':
            continue  # Based on constraints, only Thursday is possible
        if day == 'Thursday':
            # Check possible time slots after 15:00
            possible_times = [
                (15*60, 15*60 + 30),
                (15*60 + 30, 16*60),
                (16*60, 16*60 + 30)
            ]
            for slot in possible_times:
                start, end = slot
                if is_free(betty_schedule, day, start, end) and is_free(scott_schedule, day, start, end):
                    # Format the output
                    meeting_start = minutes_to_time(start)
                    meeting_end = minutes_to_time(end)
                    print(f"{meeting_start}:{meeting_end}:{day}")
                    return

find_meeting_time()