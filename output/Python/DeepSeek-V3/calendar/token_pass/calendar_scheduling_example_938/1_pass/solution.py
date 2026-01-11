from datetime import time

def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return time(h, mm)

def busy_to_intervals(busy_list, day_start, day_end):
    # busy_list: list of (start, end) time tuples for that day
    # day_start, day_end: time objects
    free = []
    last_end = day_start
    for start_t, end_t in sorted(busy_list, key=lambda x: x[0]):
        if last_end < start_t:
            free.append((last_end, start_t))
        last_end = max(last_end, end_t)
    if last_end < day_end:
        free.append((last_end, day_end))
    return free

def intersect_intervals(free1, free2, duration_min):
    # free1, free2: list of (start, end) time intervals
    # return overlapping intervals of at least duration_min
    overlaps = []
    for s1, e1 in free1:
        for s2, e2 in free2:
            start_overlap = max(s1, s2)
            end_overlap = min(e1, e2)
            if start_overlap < end_overlap:
                if (time_to_minutes(end_overlap) - time_to_minutes(start_overlap)) >= duration_min:
                    overlaps.append((start_overlap, end_overlap))
    return overlaps

def main():
    # Work hours 9:00 to 17:00
    work_start = time(9, 0)
    work_end = time(17, 0)
    duration = 30  # minutes
    
    # Days to check in order of preference (Eric prefers not Wednesday)
    days_order = ["Friday", "Wednesday", "Monday", "Tuesday", "Thursday"]
    
    # Eugene's busy times per day
    eugene_busy = {
        "Monday": [(time(11, 0), time(12, 0)), (time(13, 30), time(14, 0)), 
                   (time(14, 30), time(15, 0)), (time(16, 0), time(16, 30))],
        "Wednesday": [(time(9, 0), time(9, 30)), (time(11, 0), time(11, 30)),
                      (time(12, 0), time(12, 30)), (time(13, 30), time(15, 0))],
        "Thursday": [(time(9, 30), time(10, 0)), (time(11, 0), time(12, 30))],
        "Friday": [(time(10, 30), time(11, 0)), (time(12, 0), time(12, 30)),
                   (time(13, 0), time(13, 30))],
        "Tuesday": []  # No busy times given
    }
    
    # Eric's busy times per day
    eric_busy = {
        "Monday": [(time(9, 0), time(17, 0))],
        "Tuesday": [(time(9, 0), time(17, 0))],
        "Wednesday": [(time(9, 0), time(11, 30)), (time(12, 0), time(14, 0)),
                      (time(14, 30), time(16, 30))],
        "Thursday": [(time(9, 0), time(17, 0))],
        "Friday": [(time(9, 0), time(11, 0)), (time(11, 30), time(17, 0))]
    }
    
    for day in days_order:
        # Free intervals for Eugene
        eugene_free = busy_to_intervals(eugene_busy.get(day, []), work_start, work_end)
        # Free intervals for Eric
        eric_free = busy_to_intervals(eric_busy.get(day, []), work_start, work_end)
        
        overlaps = intersect_intervals(eugene_free, eric_free, duration)
        if overlaps:
            # Take the first available slot
            start_meeting = overlaps[0][0]
            end_meeting = minutes_to_time(time_to_minutes(start_meeting) + duration)
            print(f"{day}: {start_meeting.strftime('%H:%M')}:{end_meeting.strftime('%H:%M')}")
            return
    
    print("No suitable time found.")

if __name__ == "__main__":
    main()