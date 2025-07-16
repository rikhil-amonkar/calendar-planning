def find_meeting_time(judy_schedule, nicole_schedule, preferred_start, meeting_duration, work_start, work_end):
    # Convert times to minutes for easier calculation
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    work_start_minutes = time_to_minutes(work_start)
    work_end_minutes = time_to_minutes(work_end)
    preferred_start_minutes = time_to_minutes(preferred_start)
    meeting_duration_minutes = int(meeting_duration * 60)  # Convert hours to minutes

    # Function to get free slots from busy slots
    def get_free_slots(busy_slots, start, end):
        free_slots = []
        current_start = start
        for busy_start, busy_end in busy_slots:
            if current_start < busy_start:
                free_slots.append((current_start, busy_start))
            current_start = max(current_start, busy_end)
        if current_start < end:
            free_slots.append((current_start, end))
        return free_slots

    # Find available slots for Nicole
    nicole_busy_slots = [(time_to_minutes(start), time_to_minutes(end)) for start, end in nicole_schedule]
    nicole_busy_slots.sort()
    nicole_free_slots = get_free_slots(nicole_busy_slots, work_start_minutes, work_end_minutes)

    # Judy's schedule is entirely free, so her free slots are just the work hours
    judy_free_slots = [(work_start_minutes, work_end_minutes)]

    # Find common free slots between Judy and Nicole
    common_free_slots = []
    i, j = 0, 0
    while i < len(judy_free_slots) and j < len(nicole_free_slots):
        start_max = max(judy_free_slots[i][0], nicole_free_slots[j][0])
        end_min = min(judy_free_slots[i][1], nicole_free_slots[j][1])
        if start_max < end_min:
            common_free_slots.append((start_max, end_min))
        if judy_free_slots[i][1] < nicole_free_slots[j][1]:
            i += 1
        else:
            j += 1

    # Check for available slot for meeting
    for start, end in common_free_slots:
        if start >= preferred_start_minutes and end - start >= meeting_duration_minutes:
            start_time = minutes_to_time(start)
            end_time = minutes_to_time(start)
            return f"{start_time}-{minutes_to_time(start + meeting_duration_minutes)}", "Monday"
        elif start < preferred_start_minutes and end - preferred_start_minutes >= meeting_duration_minutes:
            start_time = minutes_to_time(preferred_start_minutes)
            end_time = minutes_to_time(preferred_start_minutes + meeting_duration_minutes)
            return f"{start_time}-{end_time}", "Monday"

    # If no suitable time is found, return None
    return None, None

# Judy's schedule (entire day free)
judy_schedule = []

# Nicole's schedule
nicole_schedule = [("09:00", "10:00"), ("10:30", "16:30")]

# Preferred start time and meeting duration
preferred_start = "16:00"
meeting_duration = 0.5  # in hours

# Work hours
work_start = "09:00"
work_end = "17:00"

# Find and print the meeting time
meeting_time, day = find_meeting_time(judy_schedule, nicole_schedule, preferred_start, meeting_duration, work_start, work_end)

if meeting_time is not None:
    print(f"Meeting time: {meeting_time} on {day}")
else:
    print("No suitable meeting time found.")