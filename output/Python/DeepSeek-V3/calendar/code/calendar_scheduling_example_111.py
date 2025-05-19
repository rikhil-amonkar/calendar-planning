def find_meeting_time(participants_schedules, day, work_start, work_end, duration_minutes):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration = duration_minutes
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = interval
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_intervals.append((start_min, end_min))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                new_end = max(last_end, current_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append(interval)
    
    # Find available slots by checking gaps between merged intervals and work hours
    available_slots = []
    prev_end = work_start_min
    
    for interval in merged:
        start, end = interval
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end_min:
        available_slots.append((prev_end, work_end_min))
    
    # Find the first available slot that can fit the meeting
    for slot in available_slots:
        start, end = slot
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            return f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    
    return None

# Define the participants' schedules
gregory_schedule = [
    ("09:00", "10:00"),
    ("10:30", "11:30"),
    ("12:30", "13:00"),
    ("13:30", "14:00")
]

natalie_schedule = []  # Wide open

christine_schedule = [
    ("09:00", "11:30"),
    ("13:30", "17:00")
]

vincent_schedule = [
    ("09:00", "09:30"),
    ("10:30", "12:00"),
    ("12:30", "14:00"),
    ("14:30", "17:00")
]

# Combine all schedules
participants_schedules = [
    gregory_schedule,
    natalie_schedule,
    christine_schedule,
    vincent_schedule
]

# Find the meeting time
meeting_time = find_meeting_time(
    participants_schedules,
    day="Monday",
    work_start="09:00",
    work_end="17:00",
    duration_minutes=30
)

# Output the result
print(f"{meeting_time}:Monday")