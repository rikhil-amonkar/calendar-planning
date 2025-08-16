def find_meeting_time(joshua_schedule, joyce_schedule, preferred_day, meeting_duration):
    work_hours_start = 9
    work_hours_end = 17
    
    # Convert meeting duration from hours to minutes
    meeting_duration_minutes = int(meeting_duration * 60)
    
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        if day == preferred_day:
            start_check = 12  # Joyce prefers not to meet before 12:00 on Monday
        else:
            start_check = work_hours_start
        
        for hour in range(start_check, work_hours_end - meeting_duration_minutes // 60 + 1):
            for minute in [0, 30]:
                start_time = hour * 60 + minute
                end_time = start_time + meeting_duration_minutes
                
                joshua_busy = any(start_time <= j[0] < end_time or start_time < j[1] <= end_time for j in joshua_schedule.get(day, []))
                joyce_busy = any(start_time <= jo[0] < end_time or start_time < jo[1] <= end_time for jo in joyce_schedule.get(day, []))
                
                if not joshua_busy and not joyce_busy:
                    start_hour, start_minute = divmod(start_time, 60)
                    end_hour, end_minute = divmod(end_time, 60)
                    return f"{start_hour:02}:{start_minute:02}-{end_hour:02}:{end_minute:02}", day

joshua_schedule = {
    'Monday': [(15*60, 15*60 + 30)],
    'Tuesday': [(11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60 + 30, 15*60)],
    'Wednesday': []
}

joyce_schedule = {
    'Monday': [(9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 17*60)],
    'Tuesday': [(9*60, 17*60)],
    'Wednesday': [(9*60, 9*60 + 30), (10*60, 11*60), (12*60 + 30, 15*60), (16*60, 16*60 + 30)]
}

meeting_duration = 0.5  # in hours

time, day = find_meeting_time(joshua_schedule, joyce_schedule, 'Monday', meeting_duration)
print(f"Meeting time: {time} on {day}")