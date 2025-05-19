def find_meeting_time():
    # Define the work hours in minutes since midnight
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00

    # Meeting duration in minutes
    meeting_duration = 30

    # Participants' busy intervals on Monday in minutes since midnight
    jeffrey_busy = [
        (9 * 60 + 30, 10 * 60),   # 9:30-10:00
        (10 * 60 + 30, 11 * 60)   # 10:30-11:00
    ]
    virginia_busy = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (10 * 60, 10 * 60 + 30),  # 10:00-10:30
        (14 * 60 + 30, 15 * 60),  # 14:30-15:00
        (16 * 60, 16 * 60 + 30)   # 16:00-16:30
    ]
    melissa_busy = [
        (9 * 60, 11 * 60 + 30),   # 9:00-11:30
        (12 * 60, 12 * 60 + 30),  # 12:00-12:30
        (13 * 60, 15 * 60),       # 13:00-15:00
        (16 * 60, 17 * 60)        # 16:00-17:00
    ]

    # Melissa's preference: no meetings after 14:00
    latest_start = 14 * 60  # 14:00

    # Function to convert minutes to HH:MM format
    def minutes_to_time(minutes):
        return f"{minutes // 60:02d}:{minutes % 60:02d}"

    # Function to check if a time slot is free for a person
    def is_time_free(busy_intervals, start_time, end_time):
        if end_time > work_end or start_time < work_start:
            return False
        for busy_start, busy_end in busy_intervals:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True

    # Find common free time slots
    time_slots = []
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        end_time = current_time + meeting_duration
        # Check Melissa's preference
        if current_time > latest_start:
            break
        # Check if all participants are free
        if (is_time_free(jeffrey_busy, current_time, end_time) and
            is_time_free(virginia_busy, current_time, end_time) and
            is_time_free(melissa_busy, current_time, end_time)):
            time_slots.append((current_time, end_time))
        current_time += 30  # Check every 30 minutes

    # If any time slots found, return the first one
    if time_slots:
        start, end = time_slots[0]
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        return f"{start_time}:{end_time} on Monday"

    return "No common time slot found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)