def find_meeting_time(participants_schedules, work_hours, duration):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # Subtract 540 to start from 0 at 9:00

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize a list to mark busy times (in minutes)
    work_start = time_to_minutes(work_hours[0])
    work_end = time_to_minutes(work_hours[1])
    time_slots = [True] * (work_end - work_start)  # True means available

    # Mark busy times for each participant
    for schedule in participants_schedules:
        for busy_start, busy_end in schedule:
            start = max(time_to_minutes(busy_start), work_start)
            end = min(time_to_minutes(busy_end), work_end)
            for i in range(start, end):
                if i < len(time_slots):
                    time_slots[i] = False

    # Find the first available slot of duration
    duration_min = duration * 60
    current_start = None
    consecutive_available = 0

    for i in range(len(time_slots)):
        if time_slots[i]:
            if current_start is None:
                current_start = i
            consecutive_available += 1
            if consecutive_available >= duration_min:
                meeting_start = minutes_to_time(current_start)
                meeting_end = minutes_to_time(current_start + duration_min)
                return f"{meeting_start}:{meeting_end}"
        else:
            current_start = None
            consecutive_available = 0

    return "No available slot found"

# Define work hours and meeting duration
work_hours = ("9:00", "17:00")
duration = 1  # in hours

# Define participants' schedules
participants_schedules = [
    [("10:00", "10:30"), ("16:00", "16:30")],  # Stephanie
    [("10:00", "10:30"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:30", "17:00")],  # Cheryl
    [("9:30", "10:00"), ("10:30", "11:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],  # Bradley
    [("9:00", "12:00"), ("13:00", "13:30"), ("14:30", "17:00")]  # Steven
]

# Find and print the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours, duration)
print(f"Monday {meeting_time}")