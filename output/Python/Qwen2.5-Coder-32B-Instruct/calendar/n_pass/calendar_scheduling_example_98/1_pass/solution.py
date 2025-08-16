from datetime import datetime, timedelta

def find_meeting_time(juan_schedule, marilyn_schedule, ronald_schedule, meeting_duration, max_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime(max_end_time, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)

    def parse_schedule(schedule):
        return [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in schedule]

    juan_schedule = parse_schedule(juan_schedule)
    marilyn_schedule = parse_schedule(marilyn_schedule)
    ronald_schedule = parse_schedule(ronald_schedule)

    def is_free(time, schedules):
        for start, end in schedules:
            if start <= time < end:
                return False
        return True

    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if (is_free(current_time, juan_schedule) and
            is_free(current_time, marilyn_schedule) and
            is_free(current_time, ronald_schedule)):
            meeting_start = current_time.strftime("%H:%M")
            meeting_end = (current_time + meeting_duration).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end} Monday"
        current_time += timedelta(minutes=15)

    return "No available time found"

juan_schedule = [("09:00", "10:30"), ("15:30", "16:00")]
marilyn_schedule = [("11:00", "11:30"), ("12:30", "13:00")]
ronald_schedule = [("09:00", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")]

print(find_meeting_time(juan_schedule, marilyn_schedule, ronald_schedule, 30, "16:00"))