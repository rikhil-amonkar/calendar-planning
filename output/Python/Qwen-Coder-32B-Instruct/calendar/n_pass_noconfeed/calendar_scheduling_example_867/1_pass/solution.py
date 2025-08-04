def find_meeting_time(betty_schedule, scott_schedule, meeting_duration):
    work_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60   # 17:00 in minutes
    
    def parse_schedule(schedule):
        parsed = {}
        for day, times in schedule.items():
            parsed[day] = []
            for start_str, end_str in times:
                start = int(start_str.split(':')[0]) * 60 + int(start_str.split(':')[1])
                end = int(end_str.split(':')[0]) * 60 + int(end_str.split(':')[1])
                parsed[day].append((start, end))
        return parsed

    betty_schedule = parse_schedule(betty_schedule)
    scott_schedule = parse_schedule(scott_schedule)

    for day in work_days:
        if day == 'Monday':
            continue  # Betty cannot meet on Monday
        
        betty_busy = betty_schedule.get(day, [])
        scott_busy = scott_schedule.get(day, [])
        
        combined_busy = sorted(betty_busy + scott_busy)
        last_end = work_hours_start
        
        for start, end in combined_busy:
            if start - last_end >= meeting_duration:
                meeting_start = last_end
                meeting_end = meeting_start + meeting_duration
                meeting_start_formatted = f"{meeting_start // 60:02}:{meeting_start % 60:02}"
                meeting_end_formatted = f"{meeting_end // 60:02}:{meeting_end % 60:02}"
                
                if day == 'Wednesday' and scott_busy:
                    continue  # Scott prefers not to have more meetings on Wednesday
                
                if day == 'Thursday' and meeting_start < 15 * 60:
                    continue  # Scott cannot meet before 15:00 on Thursday
                
                return f"{meeting_start_formatted}:{meeting_end_formatted}", day
            
            last_end = max(last_end, end)
    
    return None, None

betty_schedule = {
    'Monday': [('10:00', '10:30'), ('13:30', '14:00'), ('15:00', '15:30'), ('16:00', '16:30')],
    'Tuesday': [('9:00', '9:30'), ('11:30', '12:00'), ('12:30', '13:00'), ('13:30', '14:00'), ('16:30', '17:00')],
    'Wednesday': [('9:30', '10:30'), ('13:00', '13:30'), ('14:00', '14:30')],
    'Thursday': [('9:30', '10:00'), ('11:30', '12:00'), ('14:00', '14:30'), ('15:00', '15:30'), ('16:30', '17:00')]
}

scott_schedule = {
    'Monday': [('9:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')],
    'Tuesday': [('9:00', '9:30'), ('10:00', '11:00'), ('11:30', '12:00'), ('12:30', '13:30'), ('14:00', '15:00'), ('16:00', '16:30')],
    'Wednesday': [('9:30', '12:30'), ('13:00', '13:30'), ('14:00', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')],
    'Thursday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '12:00'), ('12:30', '13:00'), ('15:00', '16:00'), ('16:30', '17:00')]
}

meeting_duration = 30  # in minutes
time, day = find_meeting_time(betty_schedule, scott_schedule, meeting_duration)
print(f"{time}, {day}")