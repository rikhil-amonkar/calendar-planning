def find_meeting_time(carl_schedule, margaret_schedule, meeting_duration, preferred_days, carl_avoid_day):
    work_start = 9
    work_end = 17

    for day in preferred_days:
        if day == carl_avoid_day:
            continue

        carl_busy_times = carl_schedule[day]
        margaret_busy_times = margaret_schedule[day]

        carl_free_times = []
        margaret_free_times = []

        # Calculate free times for Carl
        start = work_start
        for busy_start, busy_end in carl_busy_times:
            if start < busy_start:
                carl_free_times.append((start, busy_start))
            start = busy_end
        if start < work_end:
            carl_free_times.append((start, work_end))

        # Calculate free times for Margaret
        start = work_start
        for busy_start, busy_end in margaret_busy_times:
            if start < busy_start:
                margaret_free_times.append((start, busy_start))
            start = busy_end
        if start < work_end:
            margaret_free_times.append((start, work_end))

        # Find common free time
        i, j = 0, 0
        while i < len(carl_free_times) and j < len(margaret_free_times):
            carl_start, carl_end = carl_free_times[i]
            margaret_start, margaret_end = margaret_free_times[j]

            overlap_start = max(carl_start, margaret_start)
            overlap_end = min(carl_end, margaret_end)

            if overlap_end - overlap_start >= meeting_duration:
                return f"{overlap_start:02}:{overlap_start + meeting_duration:02}:00", day

            if carl_end < margaret_end:
                i += 1
            else:
                j += 1

    return None, None

# Define the schedules
carl_schedule = {
    "Monday": [(11, 11.5)],
    "Tuesday": [(14.5, 15)],
    "Wednesday": [(10, 11.5), (13, 13.5)],
    "Thursday": [(13.5, 14), (16, 16.5)]
}

margaret_schedule = {
    "Monday": [(9, 10.5), (11, 17)],
    "Tuesday": [(9.5, 12), (13.5, 14), (15.5, 17)],
    "Wednesday": [(9.5, 12), (12.5, 13), (13.5, 14.5), (15, 17)],
    "Thursday": [(10, 12), (12.5, 14), (14.5, 17)]
}

meeting_duration = 1
preferred_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
carl_avoid_day = "Thursday"

time, day = find_meeting_time(carl_schedule, margaret_schedule, meeting_duration, preferred_days, carl_avoid_day)
print(f"Meeting Time: {time}, Day: {day}")