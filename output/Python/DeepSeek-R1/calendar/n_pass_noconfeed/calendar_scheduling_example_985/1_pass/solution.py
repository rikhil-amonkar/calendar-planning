def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [[work_start, work_end]]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for interval in sorted_busy:
        s, e = interval
        if current_start < s:
            free.append([current_start, s])
        current_start = max(current_start, e)
    if current_start < work_end:
        free.append([current_start, work_end])
    return free

def main():
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = time_str_to_minutes("9:00")  # 540 minutes
    work_end = time_str_to_minutes("17:00")   # 1020 minutes
    wednesday_constraint = time_str_to_minutes("12:30")  # 750 minutes

    diane_busy = {
        "Monday": [("12:00", "12:30"), ("15:00", "15:30")],
        "Tuesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("16:00", "17:00")],
        "Wednesday": [("9:00", "9:30"), ("14:30", "15:00"), ("16:30", "17:00")],
        "Thursday": [("15:30", "16:30")],
        "Friday": [("9:30", "11:30"), ("14:30", "15:00"), ("16:00", "17:00")]
    }

    matthew_busy = {
        "Monday": [("9:00", "10:00"), ("10:30", "17:00")],
        "Tuesday": [("9:00", "17:00")],
        "Wednesday": [("9:00", "11:00"), ("12:00", "14:30"), ("16:00", "17:00")],
        "Thursday": [("9:00", "16:00")],
        "Friday": [("9:00", "17:00")]
    }

    # Convert busy times to minutes for each day
    diane_busy_min = {}
    matthew_busy_min = {}
    for day in days:
        diane_busy_min[day] = []
        for s, e in diane_busy[day]:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            diane_busy_min[day].append([s_min, e_min])
        
        matthew_busy_min[day] = []
        for s, e in matthew_busy[day]:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            matthew_busy_min[day].append([s_min, e_min])
    
    for day in days:
        free_diane = get_free_intervals(diane_busy_min[day], work_start, work_end)
        free_matthew = get_free_intervals(matthew_busy_min[day], work_start, work_end)
        
        common_free = []
        for interval_d in free_diane:
            for interval_m in free_matthew:
                low = max(interval_d[0], interval_m[0])
                high = min(interval_d[1], interval_m[1])
                if low < high:
                    common_free.append([low, high])
        
        for interval in common_free:
            start, end = interval
            if day == "Wednesday":
                candidate_start = max(start, wednesday_constraint)
            else:
                candidate_start = start
                
            if candidate_start + 60 <= end:
                meeting_start = candidate_start
                meeting_end = candidate_start + 60
                start_str = minutes_to_time_str(meeting_start)
                end_str = minutes_to_time_str(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return

if __name__ == "__main__":
    main()