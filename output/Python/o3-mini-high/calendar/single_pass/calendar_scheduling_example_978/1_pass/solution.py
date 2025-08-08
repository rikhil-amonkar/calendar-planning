def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    for interval in sorted(busy):
        b_start, b_end = interval
        if current < b_start:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_common = max(start1, start2)
        end_common = min(end1, end2)
        if start_common < end_common:
            common.append((start_common, end_common))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return common

def find_slot(intervals, duration):
    for start, end in intervals:
        if end - start >= duration:
            return start, start + duration
    return None

def main():
    # meeting settings
    meeting_duration = 60  # in minutes
    work_start = 9 * 60    # 09:00 in minutes (9*60=540)
    work_end = 17 * 60     # 17:00 in minutes (17*60=1020)
    
    # Busy schedules given as (start, end) in minutes.
    # Brian's busy schedule
    brian_schedule = {
        "Monday": [(570, 600), (750, 870), (930, 960)],           # 9:30-10:00, 12:30-14:30, 15:30-16:00
        "Tuesday": [(540, 570)],                                    # 9:00-9:30
        "Wednesday": [(750, 840), (990, 1020)],                     # 12:30-14:00, 16:30-17:00
        "Thursday": [(660, 690), (780, 810), (990, 1020)],           # 11:00-11:30, 13:00-13:30, 16:30-17:00
        "Friday": [(570, 600), (630, 660), (780, 810), (900, 960), (990, 1020)]
        # 9:30-10:00, 10:30-11:00, 13:00-13:30, 15:00-16:00, 16:30-17:00
    }
    
    # Julia's busy schedule
    julia_schedule = {
        "Monday": [(540, 600), (660, 690), (750, 780), (930, 960)],  # 9:00-10:00, 11:00-11:30, 12:30-13:00, 15:30-16:00
        "Tuesday": [(780, 840), (960, 990)],                          # 13:00-14:00, 16:00-16:30
        "Wednesday": [(540, 690), (720, 750), (780, 1020)],           # 9:00-11:30, 12:00-12:30, 13:00-17:00
        "Thursday": [(540, 630), (660, 1020)],                        # 9:00-10:30, 11:00-17:00
        "Friday": [(540, 600), (630, 690), (750, 840), (870, 900), (930, 960)]
        # 9:00-10:00, 10:30-11:30, 12:30-14:00, 14:30-15:00, 15:30-16:00
    }
    
    # Brian wants to avoid Monday so check the days in this order:
    days_to_check = ["Tuesday", "Wednesday", "Thursday", "Friday", "Monday"]
    
    meeting_day = None
    meeting_time = None
    
    for day in days_to_check:
        # Get each persons' busy intervals for the day (defaults to [] if day is not found)
        brian_busy = brian_schedule.get(day, [])
        julia_busy = julia_schedule.get(day, [])
        
        # Compute free intervals for each participant
        brian_free = get_free_intervals(brian_busy, work_start, work_end)
        julia_free = get_free_intervals(julia_busy, work_start, work_end)
        
        # Find common free intervals by intersecting their free times
        common_free = intersect_intervals(brian_free, julia_free)
        
        slot = find_slot(common_free, meeting_duration)
        if slot:
            meeting_day = day
            meeting_time = slot
            break

    if meeting_day and meeting_time:
        start, end = meeting_time
        start_str = minutes_to_time(start)
        end_str = minutes_to_time(end)
        # The output format includes both the time range (as {HH:MM:HH:MM})
        # and the day of the week.
        print(f"{meeting_day} {{{start_str}:{end_str}}}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()