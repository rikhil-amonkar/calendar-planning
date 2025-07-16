def find_meeting_time(natalie_schedule, william_schedule, meeting_duration):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    for day in days:
        natalie_busy = natalie_schedule[day]
        william_busy = william_schedule[day]
        
        natalie_free = find_free_times(natalie_busy, work_start, work_end)
        william_free = find_free_times(william_busy, work_start, work_end)
        
        common_free = find_common_free_times(natalie_free, william_free)
        
        for start, end in common_free:
            if end - start >= meeting_duration:
                start_time = f"{start // 60:02}:{start % 60:02}"
                end_time = f"{(start + meeting_duration) // 60:02}:{(start + meeting_duration) % 60:02}"
                return f"{start_time}:{end_time} {day}"

def find_free_times(busy_times, work_start, work_end):
    free_times = []
    current_start = work_start
    
    for start, end in busy_times:
        if start > current_start:
            free_times.append((current_start, start))
        current_start = max(current_start, end)
    
    if current_start < work_end:
        free_times.append((current_start, work_end))
    
    return free_times

def find_common_free_times(free_times1, free_times2):
    common_free = []
    i, j = 0, 0
    
    while i < len(free_times1) and j < len(free_times2):
        start1, end1 = free_times1[i]
        start2, end2 = free_times2[j]
        
        common_start = max(start1, start2)
        common_end = min(end1, end2)
        
        if common_start < common_end:
            common_free.append((common_start, common_end))
        
        if end1 < end2:
            i += 1
        else:
            j += 1
    
    return common_free

natalie_schedule = {
    "Monday": [(9*60, 9*60+30), (10*60, 12*60), (12*60+30, 13*60), (14*60, 14*60+30), (15*60, 16*60+30)],
    "Tuesday": [(9*60, 9*60+30), (10*60, 10*60+30), (12*60+30, 14*60), (16*60, 17*60)],
    "Wednesday": [(11*60, 11*60+30), (16*60, 16*60+30)],
    "Thursday": [(10*60, 11*60), (11*60+30, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)]
}

william_schedule = {
    "Monday": [(9*60+30, 11*60), (11*60+30, 17*60)],
    "Tuesday": [(9*60, 13*60), (13*60+30, 16*60)],
    "Wednesday": [(9*60, 12*60+30), (13*60, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)],
    "Thursday": [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 14*60), (15*60, 17*60)]
}

meeting_duration = 60  # 1 hour in minutes
print(find_meeting_time(natalie_schedule, william_schedule, meeting_duration))