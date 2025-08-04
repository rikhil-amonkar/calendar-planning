from datetime import datetime, timedelta

def find_meeting_time(bryan_schedule, nicholas_schedule, preferred_days, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    def parse_schedule(schedule):
        parsed = {}
        for entry in schedule:
            day, time_range = entry.split(' ')
            start, end = time_range.split('-')
            if day not in parsed:
                parsed[day] = []
            parsed[day].append((datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")))
        return parsed
    
    bryan_schedule = parse_schedule(bryan_schedule)
    nicholas_schedule = parse_schedule(nicholas_schedule)
    
    def find_free_slots(schedule, day):
        slots = []
        current = work_start
        for start, end in sorted(schedule.get(day, [])):
            if current < start:
                slots.append((current, start))
            current = max(current, end)
        if current < work_end:
            slots.append((current, work_end))
        return slots
    
    for day in preferred_days:
        bryan_slots = find_free_slots(bryan_schedule, day)
        nicholas_slots = find_free_slots(nicholas_schedule, day)
        
        for b_start, b_end in bryan_slots:
            for n_start, n_end in nicholas_slots:
                common_start = max(b_start, n_start)
                common_end = min(b_end, n_end)
                if (common_end - common_start) >= timedelta(hours=meeting_duration):
                    return f"{common_start.strftime('%H:%M')}:{common_end.strftime('%H:%M')}", day
    
    return None, None

bryan_schedule = [
    "Thursday 09:30-10:00",
    "Thursday 12:30-13:00",
    "Friday 10:30-11:00",
    "Friday 14:00-14:30"
]

nicholas_schedule = [
    "Monday 11:30-12:00",
    "Monday 13:00-15:30",
    "Tuesday 09:00-09:30",
    "Tuesday 11:00-13:30",
    "Tuesday 14:00-16:30",
    "Wednesday 09:00-09:30",
    "Wednesday 10:00-11:00",
    "Wednesday 11:30-13:30",
    "Wednesday 14:00-14:30",
    "Wednesday 15:00-16:30",
    "Thursday 10:30-11:30",
    "Thursday 12:00-12:30",
    "Thursday 15:00-15:30",
    "Thursday 16:30-17:00",
    "Friday 09:00-10:30",
    "Friday 11:00-12:00",
    "Friday 12:30-14:30",
    "Friday 15:30-16:00",
    "Friday 16:30-17:00"
]

preferred_days = ["Wednesday", "Friday"]
meeting_duration = 1

time, day = find_meeting_time(bryan_schedule, nicholas_schedule, preferred_days, meeting_duration)
print(f"{time}, {day}")