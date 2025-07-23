def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day):
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
    
    # Combine all busy intervals and sort them
    all_busy = []
    for schedule in participants_schedules:
        for busy_range in schedule:
            # Split the range into start and end times
            parts = busy_range.split(':')
            start_time = f"{parts[0]}:{parts[1]}"
            end_time = f"{parts[2]}:{parts[3]}"
            start = time_to_minutes(start_time)
            end = time_to_minutes(end_time)
            all_busy.append((start, end))
    
    all_busy.sort()
    
    # Find available slots
    available_slots = []
    prev_end = work_start
    
    for start, end in all_busy:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Find the earliest slot that fits the meeting duration
    meeting_duration_min = time_to_minutes(meeting_duration)
    for slot in available_slots:
        start, end = slot
        if end - start >= meeting_duration_min:
            meeting_end = start + meeting_duration_min
            return (minutes_to_time(start), minutes_to_time(meeting_end))
    
    return None

# Define the participants' schedules
andrew_schedule = []  # Wide open
grace_schedule = []   # No meetings
samuel_schedule = [
    "09:00:10:30",
    "11:30:12:00",
    "13:00:13:30",
    "14:00:16:00",
    "16:30:17:00"
]

participants_schedules = [andrew_schedule, grace_schedule, samuel_schedule]
meeting_duration = "00:30"  # Half an hour
work_hours_start = "09:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}} {day}")
else:
    print("No suitable time found.")