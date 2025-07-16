def find_meeting_time(larry_schedule, samuel_schedule, preferred_days, meeting_duration):
    work_start = 9 * 60  # 9:00 AM in minutes
    work_end = 17 * 60   # 5:00 PM in minutes
    
    def parse_schedule(schedule):
        parsed = []
        for entry in schedule:
            start, end = entry.split('-')
            start_hour, start_minute = map(int, start.split(':'))
            end_hour, end_minute = map(int, end.split(':'))
            parsed.append((start_hour * 60 + start_minute, end_hour * 60 + end_minute))
        return parsed
    
    larry_schedule = parse_schedule(larry_schedule)
    samuel_schedule = parse_schedule(samuel_schedule)
    
    for day in preferred_days:
        if day == 'Monday':
            samuel_busy = samuel_schedule[:5]
        elif day == 'Tuesday':
            samuel_busy = samuel_schedule[5:8]
        elif day == 'Wednesday':
            samuel_busy = samuel_schedule[8:]
        
        available_slots = []
        current_time = work_start
        
        for busy_start, busy_end in samuel_busy:
            if current_time < busy_start:
                available_slots.append((current_time, busy_start))
            current_time = max(current_time, busy_end)
        
        if current_time < work_end:
            available_slots.append((current_time, work_end))
        
        for start, end in available_slots:
            if end - start >= meeting_duration:
                return f"{start // 60:02}:{start % 60:02}-{(start + meeting_duration) // 60:02}:{(start + meeting_duration) % 60:02}", day
    
    return None

larry_schedule = []  # Larry's calendar is wide open
samuel_schedule = ["10:30-11:00", "12:00-12:30", "13:00-15:00", "15:30-16:30",
                   "9:00-12:00", "14:00-15:30", "16:30-17:00",
                   "10:30-11:00", "11:30-12:00", "12:30-13:00", "14:00-14:30", "15:00-16:00"]
preferred_days = ['Monday', 'Tuesday', 'Wednesday']
meeting_duration = 30  # 30 minutes

meeting_time, meeting_day = find_meeting_time(larry_schedule, samuel_schedule, preferred_days, meeting_duration)
print(f"{meeting_time} {meeting_day}")