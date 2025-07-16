from datetime import datetime, timedelta

def find_meeting_time(gary_schedule, david_schedule, meeting_duration, work_start, work_end, days):
    meeting_duration = timedelta(hours=meeting_duration)
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")

    for day in days:
        gary_blocked = gary_schedule[day]
        david_blocked = david_schedule[day]

        gary_free_times = get_free_times(gary_blocked, work_start, work_end)
        david_free_times = get_free_times(david_blocked, work_start, work_end)

        common_free_times = find_common_free_times(gary_free_times, david_free_times)

        for start, end in common_free_times:
            if end - start >= meeting_duration:
                meeting_start = start.strftime("%H:%M")
                meeting_end = (start + meeting_duration).strftime("%H:%M")
                return f"{meeting_start}:{meeting_end} {day}"

    return "No available time found"

def get_free_times(blocked_times, work_start, work_end):
    free_times = []
    current_start = work_start

    for start, end in sorted(blocked_times):
        if current_start < start:
            free_times.append((current_start, start))
        current_start = max(current_start, end)

    if current_start < work_end:
        free_times.append((current_start, work_end))

    return free_times

def find_common_free_times(free_times1, free_times2):
    common_free_times = []
    i, j = 0, 0

    while i < len(free_times1) and j < len(free_times2):
        start1, end1 = free_times1[i]
        start2, end2 = free_times2[j]

        common_start = max(start1, start2)
        common_end = min(end1, end2)

        if common_start < common_end:
            common_free_times.append((common_start, common_end))

        if end1 <= end2:
            i += 1
        else:
            j += 1

    return common_free_times

gary_schedule = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
}

david_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

print(find_meeting_time(gary_schedule, david_schedule, 1, "09:00", "17:00", ["Monday", "Tuesday"]))