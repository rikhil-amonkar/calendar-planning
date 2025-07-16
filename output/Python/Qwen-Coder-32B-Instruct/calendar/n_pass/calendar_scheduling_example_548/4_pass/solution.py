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

    # Find available slots for Nicole
    nicole_busy_slots = []
    for start, end in nicole_schedule:
        start_minutes = time_to_minutes(start)
        end_minutes = time_to_minutes(end)
        nicole_busy_slots.append((start_minutes, end_minutes))

    # Sort Nicole's busy slots
    nicole_busy_slots.sort()

    # Merge overlapping intervals in Nicole's busy slots
    merged_nicole_busy_slots = []
    for start, end in nicole_busy_slots:
        if merged_nicole_busy_slots and start <= merged_nicole_busy_slots[-1][1]:
            merged_nicole_busy_slots[-1] = (merged_nicole_busy_slots[-1][0], max(merged_nicole_busy_slots[-1][1], end))
        else:
            merged_nicole_busy_slots.append((start, end))

    # Check for available slot for meeting
    current_time = max(work_start_minutes, preferred_start_minutes)
    while current_time + meeting_duration_minutes <= work_end_minutes:
        available = True
        for busy_start, busy_end in merged_nicole_busy_slots:
            if current_time < busy_end and current_time + meeting_duration_minutes > busy_start:
                available = False
                current_time = busy_end
                break
        if available:
            start_time = minutes_to_time(current_time)
            end_time = minutes_to_time(current_time + meeting_duration_minutes)
            return f"{start_time}-{end_time}", "Monday"
        current_time += 15  # Check every 15 minutes

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