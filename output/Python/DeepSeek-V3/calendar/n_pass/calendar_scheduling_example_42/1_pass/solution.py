def find_meeting_time(participants_schedules, work_hours, duration_minutes=60):
    # Convert all time slots to minutes since 9:00 (start of work hours)
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes - 9 * 60  # Subtract 9:00 to start from 0

    def minutes_to_time(minutes):
        total_minutes = minutes + 9 * 60  # Add back 9:00
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours:02d}:{mins:02d}"

    work_start = time_to_minutes(work_hours[0])
    work_end = time_to_minutes(work_hours[1])
    duration = duration_minutes

    # Initialize a list to mark busy times
    timeline = [False] * (work_end - work_start)

    # Mark busy times for each participant
    for schedule in participants_schedules:
        for busy_start, busy_end in schedule:
            start = max(time_to_minutes(busy_start), work_start)
            end = min(time_to_minutes(busy_end), work_end)
            for i in range(start, end):
                if i < len(timeline):
                    timeline[i] = True

    # Find the first available slot of duration
    available_start = None
    consecutive_free = 0
    for i in range(len(timeline)):
        if not timeline[i]:
            consecutive_free += 1
            if consecutive_free >= duration:
                available_start = i - duration + 1
                break
        else:
            consecutive_free = 0

    if available_start is not None:
        start_time = minutes_to_time(available_start)
        end_time = minutes_to_time(available_start + duration)
        return start_time, end_time
    else:
        return None

# Define work hours and participants' schedules
work_hours = ("9:00", "17:00")
participants_schedules = [
    [("9:00", "9:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("16:00", "17:00")],  # Julie
    [("9:00", "9:30"), ("13:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],  # Sean
    [("10:00", "10:30"), ("11:00", "13:00"), ("15:30", "17:00")],  # Lori
]

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours)
if meeting_time:
    start, end = meeting_time
    print(f"{start}:{end}")
    print("Monday")
else:
    print("No available time slot found.")