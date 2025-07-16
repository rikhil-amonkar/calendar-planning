def find_meeting_time(participant_schedules, meeting_duration, work_hours_start, work_hours_end, day):
    # Convert all times to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_minutes = meeting_duration * 60

    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participant_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(':'))
            busy_intervals.append((start, end))
    
    # Add constraints (Albert cannot meet after 11:00)
    constraint_time = time_to_minutes("11:00")
    busy_intervals.append((constraint_time, work_end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Find free slots by checking gaps between busy intervals
    previous_end = work_start
    free_slots = []
    for start, end in busy_intervals:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    # Check if there's any time left after the last busy interval
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))
    
    # Find the first free slot that can accommodate the meeting
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            start_time = minutes_to_time(meeting_start)
            end_time = minutes_to_time(meeting_end)
            return f"{start_time}:{end_time}", day
    
    return None, None

# Define the schedules and constraints
deborah_schedule = []  # Free all day
albert_schedule = ["09:00:10:00", "10:30:12:00", "15:00:16:30"]
participant_schedules = [deborah_schedule, albert_schedule]
meeting_duration = 0.5  # 30 minutes
work_hours_start = "09:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
meeting_time, day = find_meeting_time(participant_schedules, meeting_duration, work_hours_start, work_hours_end, day)

# Output the result
print(f"{meeting_time} {day}")