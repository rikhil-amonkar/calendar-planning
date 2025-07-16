from datetime import datetime, timedelta

def find_meeting_time(betty_schedule, scott_schedule, meeting_duration, preferred_days, excluded_times):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    def parse_busy_times(schedule):
        busy_times = []
        for day, times in schedule.items():
            busy_times.append((day, [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), t.split('-'))) for t in times]))
        return busy_times
    
    betty_busy = parse_busy_times(betty_schedule)
    scott_busy = parse_busy_times(scott_schedule)
    
    for day in preferred_days:
        betty_day_busy = next(filter(lambda x: x[0] == day, betty_busy), None)[1]
        scott_day_busy = next(filter(lambda x: x[0] == day, scott_busy), None)[1]
        
        current_time = work_start
        while current_time < work_end - timedelta(minutes=meeting_duration):
            available = True
            for start, end in betty_day_busy + scott_day_busy:
                if start <= current_time < end or start < current_time + timedelta(minutes=meeting_duration) <= end:
                    available = False
                    current_time = end
                    break
            if available and current_time.hour * 60 + current_time.minute not in excluded_times[day]:
                return f"{current_time.strftime('%H:%M')}:{(current_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}", day
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None, None

betty_schedule = {
    'Monday': ['10:00-10:30', '13:30-14:00', '15:00-15:30', '16:00-16:30'],
    'Tuesday': ['09:00-09:30', '11:30-12:00', '12:30-13:00', '13:30-14:00', '16:30-17:00'],
    'Wednesday': ['09:30-10:30', '13:00-13:30', '14:00-14:30'],
    'Thursday': ['09:30-10:00', '11:30-12:00', '14:00-14:30', '15:00-15:30', '16:30-17:00']
}

scott_schedule = {
    'Monday': ['09:30-15:00', '15:30-16:00', '16:30-17:00'],
    'Tuesday': ['09:00-09:30', '10:00-11:00', '11:30-12:00', '12:30-13:30', '14:00-15:00', '16:00-16:30'],
    'Wednesday': ['09:30-12:30', '13:00-13:30', '14:00-14:30', '15:00-15:30', '16:00-16:30'],
    'Thursday': ['09:00-09:30', '10:00-10:30', '11:00-12:00', '12:30-13:00', '15:00-16:00', '16:30-17:00']
}

meeting_duration = 30
preferred_days = ['Wednesday', 'Thursday']
excluded_times = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': [14*60+30],  # 14:30 in minutes
    'Thursday': list(range(9*60, 15*60))  # Before 15:00 in minutes
}

time, day = find_meeting_time(betty_schedule, scott_schedule, meeting_duration, preferred_days, excluded_times)
print(f"Meeting time: {time} on {day}")