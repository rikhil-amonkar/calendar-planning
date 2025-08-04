from datetime import datetime, timedelta

def find_meeting_time(brian_schedule, julia_schedule, meeting_duration):
    work_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    work_start = datetime.strptime('09:00', '%H:%M')
    work_end = datetime.strptime('17:00', '%H:%M')
    
    def parse_schedule(schedule):
        parsed_schedule = {}
        for day, times in schedule.items():
            parsed_schedule[day] = [tuple(map(lambda x: datetime.strptime(x, '%H:%M'), time.split('-'))) for time in times]
        return parsed_schedule
    
    brian_schedule = parse_schedule(brian_schedule)
    julia_schedule = parse_schedule(julia_schedule)
    
    for day in work_days:
        if day == 'Monday':
            continue  # Brian prefers not to have meetings on Monday
        
        brian_busy = brian_schedule.get(day, [])
        julia_busy = julia_schedule.get(day, [])
        
        current_time = work_start
        while current_time + timedelta(hours=meeting_duration) <= work_end:
            available = True
            
            for start, end in brian_busy:
                if start <= current_time < end or start < current_time + timedelta(hours=meeting_duration) <= end:
                    available = False
                    current_time = end
                    break
            
            for start, end in julia_busy:
                if start <= current_time < end or start < current_time + timedelta(hours=meeting_duration) <= end:
                    available = False
                    break
            
            if available:
                start_time_str = current_time.strftime('%H:%M')
                end_time_str = (current_time + timedelta(hours=meeting_duration)).strftime('%H:%M')
                return f"{start_time_str}:{end_time_str} {day}"
            
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return "No available time found"

brian_schedule = {
    'Monday': ['09:30-10:00', '12:30-14:30', '15:30-16:00'],
    'Tuesday': ['09:00-09:30'],
    'Wednesday': ['12:30-14:00', '16:30-17:00'],
    'Thursday': ['11:00-11:30', '13:00-13:30', '16:30-17:00'],
    'Friday': ['09:30-10:00', '10:30-11:00', '13:00-13:30', '15:00-16:00', '16:30-17:00']
}

julia_schedule = {
    'Monday': ['09:00-10:00', '11:00-11:30', '12:30-13:00', '15:30-16:00'],
    'Tuesday': ['13:00-14:00', '16:00-16:30'],
    'Wednesday': ['09:00-11:30', '12:00-12:30', '13:00-17:00'],
    'Thursday': ['09:00-10:30', '11:00-17:00'],
    'Friday': ['09:00-10:00', '10:30-11:30', '12:30-14:00', '14:30-15:00', '15:30-16:00']
}

meeting_duration = 1  # Meeting duration in hours
print(find_meeting_time(brian_schedule, julia_schedule, meeting_duration))