from datetime import datetime, timedelta

def find_meeting_time(terry_schedule, frances_schedule, meeting_duration, preferred_days):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    def parse_schedule(schedule):
        parsed_schedule = []
        for entry in schedule:
            day, times = entry.split(' ')
            start, end = times.split('-')
            start_time = datetime.strptime(start, "%H:%M")
            end_time = datetime.strptime(end, "%H:%M")
            parsed_schedule.append((day, start_time, end_time))
        return parsed_schedule
    
    terry_parsed = parse_schedule(terry_schedule)
    frances_parsed = parse_schedule(frances_schedule)
    
    def is_free(day, time, schedule):
        for d, start, end in schedule:
            if d == day and start <= time < end:
                return False
        return True
    
    for day in preferred_days:
        current_time = work_start
        while current_time + timedelta(minutes=meeting_duration) <= work_end:
            terry_free = is_free(day, current_time, terry_parsed)
            frances_free = is_free(day, current_time, frances_parsed)
            if terry_free and frances_free:
                start_time_str = current_time.strftime("%H:%M")
                end_time_str = (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
                return f"{start_time_str}:{end_time_str} {day}"
            current_time += timedelta(minutes=15)
    
    return "No available time found"

terry_schedule = [
    "Monday 10:30-11:00", "Monday 12:30-14:00", "Monday 15:00-17:00",
    "Tuesday 9:30-10:00", "Tuesday 10:30-11:00", "Tuesday 14:00-14:30", "Tuesday 16:00-16:30",
    "Wednesday 9:30-10:30", "Wednesday 11:00-12:00", "Wednesday 13:00-13:30", "Wednesday 15:00-16:00", "Wednesday 16:30-17:00",
    "Thursday 9:30-10:00", "Thursday 12:00-12:30", "Thursday 13:00-14:30", "Thursday 16:00-16:30",
    "Friday 9:00-11:30", "Friday 12:00-12:30", "Friday 13:30-16:00", "Friday 16:30-17:00"
]

frances_schedule = [
    "Monday 9:30-11:00", "Monday 11:30-13:00", "Monday 14:00-14:30", "Monday 15:00-16:00",
    "Tuesday 9:00-9:30", "Tuesday 10:00-10:30", "Tuesday 11:00-12:00", "Tuesday 13:00-14:30", "Tuesday 15:30-16:30",
    "Wednesday 9:30-10:00", "Wednesday 10:30-11:00", "Wednesday 11:30-16:00", "Wednesday 16:30-17:00",
    "Thursday 11:00-12:30", "Thursday 14:30-17:00",
    "Friday 9:30-10:30", "Friday 11:00-12:30", "Friday 13:00-16:00", "Friday 16:30-17:00"
]

meeting_duration = 30  # in minutes
preferred_days = ["Monday", "Wednesday", "Thursday", "Friday"]

print(find_meeting_time(terry_schedule, frances_schedule, meeting_duration, preferred_days))