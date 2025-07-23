def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, min_participants=None):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = meeting_duration * 60
    min_participants = min_participants or len(participants_schedules)

    # Create a timeline of availability
    timeline = []
    for i, schedule in enumerate(participants_schedules):
        for busy in schedule:
            start = time_to_minutes(busy[0])
            end = time_to_minutes(busy[1])
            timeline.append((start, 1, i))  # 1 means busy starts
            timeline.append((end, -1, i))   # -1 means busy ends

    # Sort timeline (by time, then by event type)
    timeline.sort()

    current_time = work_start
    available_participants = set(range(len(participants_schedules)))
    result = None

    for time, delta, participant in timeline:
        if time > current_time:
            # Check if we have enough participants available for the duration
            if len(available_participants) >= min_participants:
                if time - current_time >= duration:
                    return (minutes_to_time(current_time), minutes_to_time(current_time + duration))
        
        # Update available participants
        if delta == 1:
            available_participants.discard(participant)
        else:
            available_participants.add(participant)
        
        current_time = max(current_time, time)

    # Check the final segment
    if work_end - current_time >= duration and len(available_participants) >= min_participants:
        return (minutes_to_time(current_time), minutes_to_time(current_time + duration))

    return None

# Example participants' schedules (busy times)
participants_schedules = [
    [("09:00", "10:30"), ("12:00", "13:00"), ("16:00", "18:00")],  # Participant 1
    [("10:00", "11:30"), ("12:30", "14:30"), ("14:30", "15:00"), ("16:00", "17:00")],  # Participant 2
    [("08:00", "09:30"), ("10:30", "12:00"), ("14:00", "15:30")],  # Participant 3
    [("09:15", "11:00"), ("12:00", "12:30"), ("15:00", "16:30")],  # Participant 4
    [("10:30", "12:00"), ("13:00", "14:00"), ("15:00", "16:30")],  # Participant 5
    [("08:30", "10:00"), ("11:00", "12:30"), ("13:30", "15:00")],  # Participant 6
]

# Meeting parameters
meeting_duration = 1  # in hours
work_hours_start = "08:00"
work_hours_end = "18:00"

# Now try with at least 5 participants available
result = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, min_participants=5)
if result:
    start_time, end_time = result
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No suitable time found.")