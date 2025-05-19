def find_meeting_time():
    # Define the work hours in minutes since midnight
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00

    # Meeting duration in minutes
    meeting_duration = 30

    # Amanda's busy intervals on Monday and Tuesday
    amanda_busy = {
        'Monday': [(9*60, 10*60 + 30),  # 9:00-10:30
                   (11*60, 11*60 + 30),  # 11:00-11:30
                   (12*60 + 30, 13*60),  # 12:30-13:00
                   (13*60 + 30, 14*60),  # 13:30-14:00
                   (14*60 + 30, 15*60),  # 14:30-15:00
                   (16*60, 16*60 + 30)], # 16:00-16:30
        'Tuesday': [(9*60, 9*60 + 30),    # 9:00-9:30
                    (10*60, 10*60 + 30),  # 10:00-10:30
                    (11*60 + 30, 12*60),  # 11:30-12:00
                    (13*60 + 30, 14*60 + 30), # 13:30-14:30
                    (15*60 + 30, 16*60),  # 15:30-16:00
                    (16*60 + 30, 17*60)]  # 16:30-17:00
    }

    # Nathan's busy intervals on Monday and Tuesday
    nathan_busy = {
        'Monday': [(10*60, 10*60 + 30), # 10:00-10:30
                   (11*60, 11*60 + 30),  # 11:00-11:30
                   (13*60 + 30, 14*60 + 30), # 13:30-14:30
                   (16*60, 16*60 + 30)], # 16:00-16:30
        'Tuesday': [(9*60, 10*60 + 30),   # 9:00-10:30
                    (11*60, 13*60),       # 11:00-13:00
                    (13*60 + 30, 14*60),  # 13:30-14:00
                    (14*60 + 30, 15*60 + 30), # 14:30-15:30
                    (16*60, 16*60 + 30)]  # 16:00-16:30
    }

    # Amanda's constraints
    amanda_constraints = {
        'Tuesday': ('max_time', 11 * 60)  # Can't meet after 11:00 on Tuesday
    }

    # Nathan's constraints
    nathan_constraints = {
        'Monday': ('cannot_meet',)  # Can't meet on Monday
    }

    # Function to convert minutes to HH:MM format
    def minutes_to_time(minutes):
        return f"{minutes // 60:02d}:{minutes % 60:02d}"

    # Function to check if a time slot is free for a person
    def is_time_free(person_busy, day, start_time, end_time):
        if end_time > work_end or start_time < work_start:
            return False
        for busy_start, busy_end in person_busy.get(day, []):
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True

    # Find common free time slots
    for day in ['Monday', 'Tuesday']:
        # Skip days where Nathan cannot meet
        if day in nathan_constraints.get('cannot_meet', []):
            continue

        # Generate all possible time slots for the day
        time_slots = []
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            end_time = current_time + meeting_duration
            # Check Amanda's constraints
            if day == 'Tuesday' and current_time > amanda_constraints['Tuesday'][1]:
                break
            # Check if both are free
            if (is_time_free(amanda_busy, day, current_time, end_time) and
                is_time_free(nathan_busy, day, current_time, end_time)):
                time_slots.append((current_time, end_time))
            current_time += 30  # Check every 30 minutes

        # If any time slots found, return the first one
        if time_slots:
            start, end = time_slots[0]
            start_time = minutes_to_time(start)
            end_time = minutes_to_time(end)
            return f"{start_time}:{end_time} on {day}"

    return "No common time slot found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)