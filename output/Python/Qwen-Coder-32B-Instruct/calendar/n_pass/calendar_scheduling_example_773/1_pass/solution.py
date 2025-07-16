from datetime import datetime, timedelta

def find_meeting_time(patrick_schedule, roy_schedule, meeting_duration, work_start, work_end, days):
    meeting_duration = timedelta(hours=meeting_duration)
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")

    for day in days:
        patrick_availability = [(work_start, work_end)]
        roy_availability = [(work_start, work_end)]

        # Remove Patrick's busy times (he's free all week, so no removal needed)
        # Remove Roy's busy times
        for busy_start, busy_end in roy_schedule[day]:
            busy_start = datetime.strptime(busy_start, "%H:%M")
            busy_end = datetime.strptime(busy_end, "%H:%M")
            new_roy_availability = []
            for start, end in roy_availability:
                if busy_start > start:
                    new_roy_availability.append((start, busy_start))
                if busy_end < end:
                    new_roy_availability.append((busy_end, end))
            roy_availability = new_roy_availability

        # Find common availability
        for p_start, p_end in patrick_availability:
            for r_start, r_end in roy_availability:
                common_start = max(p_start, r_start)
                common_end = min(p_end, r_end)
                if common_end - common_start >= meeting_duration:
                    return f"{common_start.strftime('%H:%M')}:{(common_start + meeting_duration).strftime('%H:%M')}", day

patrick_schedule = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": []
}

roy_schedule = {
    "Monday": [("10:00", "11:30"), ("12:00", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")],
    "Tuesday": [("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("9:30", "11:30"), ("12:30", "14:00"), ("14:30", "15:30"), ("16:30", "17:00")]
}

meeting_time, meeting_day = find_meeting_time(patrick_schedule, roy_schedule, 1, "09:00", "17:00", ["Monday", "Tuesday", "Wednesday"])
print(f"Meeting time: {meeting_time}, Day: {meeting_day}")