from datetime import datetime, timedelta

def find_meeting_time(nicole_schedule, daniel_schedule, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    def parse_schedule(schedule):
        parsed_schedule = {}
        for entry in schedule:
            day, time_range = entry.split(": ")
            start_time, end_time = time_range.split(" to ")
            if day not in parsed_schedule:
                parsed_schedule[day] = []
            parsed_schedule[day].append((datetime.strptime(start_time, "%H:%M"), datetime.strptime(end_time, "%H:%M")))
        return parsed_schedule
    
    nicole_schedule = parse_schedule(nicole_schedule)
    daniel_schedule = parse_schedule(daniel_schedule)
    
    def find_free_slots(schedule, day):
        if day not in schedule:
            return [(work_start, work_end)]
        slots = []
        current_start = work_start
        for start, end in sorted(schedule[day]):
            if current_start < start:
                slots.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < work_end:
            slots.append((current_start, work_end))
        return slots
    
    for day in days_of_week:
        nicole_free_slots = find_free_slots(nicole_schedule, day)
        daniel_free_slots = find_free_slots(daniel_schedule, day)
        
        for n_start, n_end in nicole_free_slots:
            for d_start, d_end in daniel_free_slots:
                overlap_start = max(n_start, d_start)
                overlap_end = min(n_end, d_end)
                if (overlap_end - overlap_start) >= timedelta(hours=meeting_duration):
                    return f"{overlap_start.strftime('%H:%M')}:{(overlap_start + timedelta(hours=meeting_duration)).strftime('%H:%M')}", day
    
    return None, None

nicole_schedule = [
    "Tuesday: 16:00 to 16:30",
    "Wednesday: 15:00 to 15:30",
    "Friday: 12:00 to 12:30",
    "Friday: 15:30 to 16:00"
]

daniel_schedule = [
    "Monday: 9:00 to 12:30",
    "Monday: 13:00 to 13:30",
    "Monday: 14:00 to 16:30",
    "Tuesday: 9:00 to 10:30",
    "Tuesday: 11:30 to 12:30",
    "Tuesday: 13:00 to 13:30",
    "Tuesday: 15:00 to 16:00",
    "Tuesday: 16:30 to 17:00",
    "Wednesday: 9:00 to 10:00",
    "Wednesday: 11:00 to 12:30",
    "Wednesday: 13:00 to 13:30",
    "Wednesday: 14:00 to 14:30",
    "Wednesday: 16:30 to 17:00",
    "Thursday: 11:00 to 12:00",
    "Thursday: 13:00 to 14:00",
    "Thursday: 15:00 to 15:30",
    "Friday: 10:00 to 11:00",
    "Friday: 11:30 to 12:00",
    "Friday: 12:30 to 14:30",
    "Friday: 15:00 to 15:30",
    "Friday: 16:00 to 16:30"
]

meeting_duration = 1
time, day = find_meeting_time(nicole_schedule, daniel_schedule, meeting_duration)
print(f"Meeting time: {time}, Day: {day}")