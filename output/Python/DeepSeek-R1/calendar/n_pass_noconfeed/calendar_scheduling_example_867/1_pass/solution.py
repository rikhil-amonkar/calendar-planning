def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_list, work_start, work_end):
    work_hours = (work_start, work_end)
    if not busy_list:
        return [(work_start, work_end)]
    
    busy_intervals = []
    for start_str, end_str in busy_list:
        s = time_to_minutes(start_str)
        e = time_to_minutes(end_str)
        s_clip = max(s, work_start)
        e_clip = min(e, work_end)
        if s_clip < e_clip:
            busy_intervals.append((s_clip, e_clip))
    
    if not busy_intervals:
        return [(work_start, work_end)]
    
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = []
    current_start = work_start
    for s, e in busy_intervals:
        if s > current_start:
            free_intervals.append((current_start, s))
        current_start = max(current_start, e)
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    return free_intervals

def main():
    work_hours_base = (9*60, 17*60)
    betty_work_hours = {
        "Thursday": (15*60, 17*60)
    }
    
    busy_times = {
        "Betty": {
            "Wednesday": [
                ("9:30", "10:30"),
                ("13:00", "13:30"),
                ("14:00", "14:30")
            ],
            "Thursday": [
                ("9:30", "10:00"),
                ("11:30", "12:00"),
                ("14:00", "14:30"),
                ("15:00", "15:30"),
                ("16:30", "17:00")
            ]
        },
        "Scott": {
            "Wednesday": [
                ("9:30", "12:30"),
                ("13:00", "13:30"),
                ("14:00", "14:30"),
                ("15:00", "15:30"),
                ("16:00", "16:30")
            ],
            "Thursday": [
                ("9:00", "9:30"),
                ("10:00", "10:30"),
                ("11:00", "12:00"),
                ("12:30", "13:00"),
                ("15:00", "16:00"),
                ("16:30", "17:00")
            ]
        }
    }
    
    days_to_check = ["Thursday", "Wednesday"]
    meeting_duration = 30
    
    for day in days_to_check:
        # Get work hours for Betty for this day
        work_betty = betty_work_hours.get(day, work_hours_base)
        # Get free intervals for Betty
        betty_busy = busy_times["Betty"].get(day, [])
        free_betty = get_free_intervals(betty_busy, work_betty[0], work_betty[1])
        
        # Scott's work hours are always base
        scott_busy = busy_times["Scott"].get(day, [])
        free_scott = get_free_intervals(scott_busy, work_hours_base[0], work_hours_base[1])
        
        # Find an overlapping free interval of at least meeting_duration
        for fb in free_betty:
            for fs in free_scott:
                start_over = max(fb[0], fs[0])
                end_over = min(fb[1], fs[1])
                if end_over - start_over >= meeting_duration:
                    start_time = minutes_to_time(start_over)
                    end_time = minutes_to_time(start_over + meeting_duration)
                    print(day)
                    print(f"{start_time}:{end_time}")
                    return
    
    # According to the problem, a solution exists, so we should always find one.
    print("No suitable time found")

if __name__ == "__main__":
    main()