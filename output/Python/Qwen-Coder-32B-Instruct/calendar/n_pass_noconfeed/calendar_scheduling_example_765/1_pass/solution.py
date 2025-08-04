def find_meeting_time(joshua_schedule, joyce_schedule, preferred_day, meeting_duration):
    work_start = 9 * 60  # 9:00 AM in minutes
    work_end = 17 * 60   # 5:00 PM in minutes
    
    days_of_week = ["Monday", "Tuesday", "Wednesday"]
    day_index = days_of_week.index(preferred_day)
    
    for day in range(day_index, len(days_of_week)):
        current_day = days_of_week[day]
        joshua_busy = joshua_schedule[current_day]
        joyce_busy = joyce_schedule[current_day]
        
        combined_busy = sorted(joshua_busy + joyce_busy)
        
        start_time = work_start
        for event in combined_busy:
            if start_time < event[0] and event[0] - start_time >= meeting_duration:
                return f"{start_time // 60:02}:{start_time % 60:02}:{(start_time + meeting_duration) // 60:02}:{(start_time + meeting_duration) % 60:02} {current_day}"
            start_time = max(start_time, event[1])
        
        if start_time + meeting_duration <= work_end:
            return f"{start_time // 60:02}:{start_time % 60:02}:{(start_time + meeting_duration) // 60:02}:{(start_time + meeting_duration) % 60:02} {current_day}"

joshua_schedule = {
    "Monday": [(15*60, 15*60+30)],
    "Tuesday": [(11*60+30, 12*60), (13*60, 13*60+30), (14*60+30, 15*60)],
    "Wednesday": []
}

joyce_schedule = {
    "Monday": [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60+30), (13*60, 15*60), (15*60+30, 17*60)],
    "Tuesday": [(9*60, 17*60)],
    "Wednesday": [(9*60, 9*60+30), (10*60, 11*60), (12*60+30, 15*60), (16*60, 16*60+30)]
}

meeting_duration = 30  # 30 minutes
preferred_day = "Wednesday"

print(find_meeting_time(joshua_schedule, joyce_schedule, preferred_day, meeting_duration))