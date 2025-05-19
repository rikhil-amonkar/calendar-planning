def find_meeting_time(participants_busy, work_hours, duration, day):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    start_work, end_work = work_hours
    start_work_min = time_to_minutes(start_work)
    end_work_min = time_to_minutes(end_work)
    duration_min = duration * 60

    # Generate all busy intervals in minutes for each participant
    busy_intervals = []
    for busy_slots in participents_busy:
        participant_busy = []
        for slot in busy_slots:
            start, end = slot
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            participant_busy.append((start_min, end_min))
        busy_intervals.append(participant_busy)

    # Find all free intervals for each participant
    free_intervals = []
    for participant in busy_intervals:
        participant_free = []
        previous_end = start_work_min
        for start, end in sorted(participant):
            if start > previous_end:
                participant_free.append((previous_end, start))
            previous_end = max(previous_end, end)
        if previous_end < end_work_min:
            participant_free.append((previous_end, end_work_min))
        free_intervals.append(participant_free)

    # Find overlapping free intervals across all participants
    common_free = free_intervals[0]
    for participant in free_intervals[1:]:
        new_common_free = []
        i = j = 0
        while i < len(common_free) and j < len(participant):
            start1, end1 = common_free[i]
            start2, end2 = participant[j]
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            if overlap_start < overlap_end:
                new_common_free.append((overlap_start, overlap_end))
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free = new_common_free

    # Find the earliest slot that fits the duration
    for start, end in common_free:
        if end - start >= duration_min:
            meeting_start = start
            meeting_end = meeting_start + duration_min
            return (
                f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}",
                day
            )
    return None

# Define the task parameters
participants_busy = [
    [("9:00", "9:30"), ("10:30", "11:00"), ("14:00", "16:00")],  # Lisa's schedule
    [("9:00", "9:30"), ("11:00", "11:30"), ("12:30", "13:30"), 
     ("14:00", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]  # Anthony's schedule
]
work_hours = ("9:00", "17:00")
duration = 30  # minutes
day = "Monday"

# Find the meeting time
meeting_time, day = find_meeting_time(participants_busy, work_hours, duration, day)
print(f"{meeting_time}:{day}")