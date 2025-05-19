def find_meeting_time(participants_busy_times, work_hours_start, work_hours_end, meeting_duration, day):
    # Convert all times to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)

    # Collect all busy times for all participants
    all_busy = []
    for busy_times in participants_busy_times:
        for start, end in busy_times:
            all_busy.append((time_to_minutes(start), time_to_minutes(end)))

    # Sort busy times by start time
    all_busy.sort()

    # Find free slots by checking gaps between busy times and work hours
    free_slots = []
    prev_end = work_start

    for start, end in all_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    if prev_end < work_end:
        free_slots.append((prev_end, work_end))

    # Check each free slot for availability
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration:
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))

    return None

# Define the participants' busy times
andrew_busy = []
grace_busy = []
samuel_busy = [
    ("09:00", "10:30"),
    ("11:30", "12:00"),
    ("13:00", "13:30"),
    ("14:00", "16:00"),
    ("16:30", "17:00")
]

participants_busy_times = [andrew_busy, grace_busy, samuel_busy]
work_hours_start = "09:00"
work_hours_end = "17:00"
meeting_duration = 30  # minutes
day = "Monday"

# Find the earliest meeting time
meeting_time = find_meeting_time(participants_busy_times, work_hours_start, work_hours_end, meeting_duration, day)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}:{day}")
else:
    print("No suitable time found.")