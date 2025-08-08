def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free_times(busy, work_start, work_end):
    # Sort busy intervals and compute free time slots within working hours.
    busy = sorted(busy, key=lambda interval: interval[0])
    free = []
    current = work_start
    for start, end in busy:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

# Define working hours and meeting duration (in minutes)
work_start = 9 * 60   # 9:00 AM in minutes
work_end = 17 * 60    # 5:00 PM in minutes
meeting_duration = 30

# Define the busy schedules for each participant (times in minutes)
schedules = {
    "Mary": {
        "Monday": [],
        "Tuesday": [(10 * 60, 10 * 60 + 30), (15 * 60 + 30, 16 * 60)],
        "Wednesday": [(9 * 60 + 30, 10 * 60), (15 * 60, 15 * 60 + 30)],
        "Thursday": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30)]
    },
    "Alexis": {
        "Monday": [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 16 * 60 + 30)],
        "Tuesday": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
        "Wednesday": [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
        "Thursday": [(10 * 60, 12 * 60), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
    }
}

# Days when the meeting can be scheduled
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

for day in days:
    # Calculate free intervals for each participant on the given day.
    participant_free = []
    for person in schedules:
        busy_intervals = schedules[person].get(day, [])
        free_intervals = compute_free_times(busy_intervals, work_start, work_end)
        participant_free.append(free_intervals)
    
    # Intersect free intervals between all participants.
    common_free = participant_free[0]
    for free_list in participant_free[1:]:
        new_common = []
        for start1, end1 in common_free:
            for start2, end2 in free_list:
                intersect_start = max(start1, start2)
                intersect_end = min(end1, end2)
                if intersect_end - intersect_start >= meeting_duration:
                    new_common.append((intersect_start, intersect_end))
        common_free = new_common
    
    # If a common free slot is found, schedule the meeting at the earliest available time.
    if common_free:
        earliest_slot = min(common_free, key=lambda x: x[0])
        meeting_start = earliest_slot[0]
        meeting_end = meeting_start + meeting_duration
        start_str = minutes_to_time_str(meeting_start)
        end_str = minutes_to_time_str(meeting_end)
        # Output in the format "Day HH:MM:HH:MM"
        print(f"{day} {start_str}:{end_str}")
        break