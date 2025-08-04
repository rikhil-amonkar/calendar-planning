def find_meeting_time(john_schedule, jennifer_schedule, meeting_duration, preferred_days):
    work_start = 9 * 60  # 9:00 AM in minutes
    work_end = 17 * 60   # 5:00 PM in minutes
    
    def parse_schedule(schedule):
        parsed = []
        for entry in schedule:
            start, end = entry.split('-')  # Corrected to split by hyphen
            start_hour, start_min = map(int, start.split(':'))
            end_hour, end_min = map(int, end.split(':'))
            parsed.append((start_hour * 60 + start_min, end_hour * 60 + end_min))
        return parsed

    john_free_times = {}
    jennifer_free_times = {}

    for day in preferred_days:
        john_free_times[day] = [(work_start, work_end)]
        jennifer_free_times[day] = [(work_start, work_end)]

    for day, schedule in john_schedule.items():
        if day in john_free_times:
            free_times = john_free_times[day]
            busy_times = parse_schedule(schedule)
            new_free_times = []
            for start, end in free_times:
                for b_start, b_end in busy_times:
                    if b_start <= start or b_end >= end:
                        continue
                    if b_start > start:
                        new_free_times.append((start, b_start))
                    if b_end < end:
                        new_free_times.append((b_end, end))
            john_free_times[day] = new_free_times

    for day, schedule in jennifer_schedule.items():
        if day in jennifer_free_times:
            free_times = jennifer_free_times[day]
            busy_times = parse_schedule(schedule)
            new_free_times = []
            for start, end in free_times:
                for b_start, b_end in busy_times:
                    if b_start <= start or b_end >= end:
                        continue
                    if b_start > start:
                        new_free_times.append((start, b_start))
                    if b_end < end:
                        new_free_times.append((b_end, end))
            jennifer_free_times[day] = new_free_times

    for day in preferred_days:
        john_times = john_free_times[day]
        jennifer_times = jennifer_free_times[day]
        for j_start, j_end in john_times:
            for je_start, je_end in jennifer_times:
                common_start = max(j_start, je_start)
                common_end = min(j_end, je_end)
                if common_end - common_start >= meeting_duration:
                    start_hour, start_min = divmod(common_start, 60)
                    end_hour, end_min = divmod(common_start + meeting_duration, 60)
                    return f"{start_hour}:{start_min:02}-{end_hour}:{end_min:02}", day

john_schedule = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': []
}

jennifer_schedule = {
    'Monday': ['9-11', '11:30-13', '13:30-14:30', '15-17'],
    'Tuesday': ['9-11:30', '12-17'],
    'Wednesday': ['9-11:30', '12-12:30', '13-14', '14:30-16', '16:30-17']
}

meeting_duration = 30  # in minutes
preferred_days = ['Monday', 'Tuesday', 'Wednesday']

time, day = find_meeting_time(john_schedule, jennifer_schedule, meeting_duration, preferred_days)
print(f"{time} {day}")