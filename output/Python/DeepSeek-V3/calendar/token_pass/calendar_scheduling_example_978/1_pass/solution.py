def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to 'HH:MM'."""
    return f"{m // 60:02d}:{m % 60:02d}"

def parse_busy_schedule(busy_list, day_start_minutes=540, day_end_minutes=1020):
    """
    busy_list: list of (start_minutes, end_minutes) within the day.
    Returns free slots within work hours.
    """
    busy_sorted = sorted(busy_list, key=lambda x: x[0])
    free = []
    current_start = day_start_minutes
    
    for start, end in busy_sorted:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < day_end_minutes:
        free.append((current_start, day_end_minutes))
    return free

def find_earliest_meeting(brian_busy, julia_busy, days_order, duration_minutes=60):
    work_start = 9 * 60   # 9:00
    work_end = 17 * 60    # 17:00
    
    for day in days_order:
        # Get free slots for Brian and Julia on this day
        brian_free = parse_busy_schedule(brian_busy[day], work_start, work_end)
        julia_free = parse_busy_schedule(julia_busy[day], work_start, work_end)
        
        # Find overlapping free slots
        for bs, be in brian_free:
            for js, je in julia_free:
                overlap_start = max(bs, js)
                overlap_end = min(be, je)
                if overlap_end - overlap_start >= duration_minutes:
                    # Found a slot
                    return day, overlap_start, overlap_start + duration_minutes
    return None

def main():
    # Define busy times in minutes from 00:00 for simplicity
    # We'll store as absolute minutes in the day (0 = 00:00, but we'll adjust to 9:00 later)
    # Actually easier: store as minutes from 0:00, then compare in day range.
    
    # Let's define day names
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    # Brian's busy times (given in HH:MM format, within day)
    brian_busy = {
        "Monday": [(time_to_minutes("9:30"), time_to_minutes("10:00")),
                   (time_to_minutes("12:30"), time_to_minutes("14:30")),
                   (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        "Tuesday": [(time_to_minutes("9:00"), time_to_minutes("9:30"))],
        "Wednesday": [(time_to_minutes("12:30"), time_to_minutes("14:00")),
                      (time_to_minutes("16:30"), time_to_minutes("17:00"))],
        "Thursday": [(time_to_minutes("11:00"), time_to_minutes("11:30")),
                     (time_to_minutes("13:00"), time_to_minutes("13:30")),
                     (time_to_minutes("16:30"), time_to_minutes("17:00"))],
        "Friday": [(time_to_minutes("9:30"), time_to_minutes("10:00")),
                   (time_to_minutes("10:30"), time_to_minutes("11:00")),
                   (time_to_minutes("13:00"), time_to_minutes("13:30")),
                   (time_to_minutes("15:00"), time_to_minutes("16:00")),
                   (time_to_minutes("16:30"), time_to_minutes("17:00"))]
    }
    
    # Julia's busy times
    julia_busy = {
        "Monday": [(time_to_minutes("9:00"), time_to_minutes("10:00")),
                   (time_to_minutes("11:00"), time_to_minutes("11:30")),
                   (time_to_minutes("12:30"), time_to_minutes("13:00")),
                   (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        "Tuesday": [(time_to_minutes("13:00"), time_to_minutes("14:00")),
                    (time_to_minutes("16:00"), time_to_minutes("16:30"))],
        "Wednesday": [(time_to_minutes("9:00"), time_to_minutes("11:30")),
                      (time_to_minutes("12:00"), time_to_minutes("12:30")),
                      (time_to_minutes("13:00"), time_to_minutes("17:00"))],
        "Thursday": [(time_to_minutes("9:00"), time_to_minutes("10:30")),
                     (time_to_minutes("11:00"), time_to_minutes("17:00"))],
        "Friday": [(time_to_minutes("9:00"), time_to_minutes("10:00")),
                   (time_to_minutes("10:30"), time_to_minutes("11:30")),
                   (time_to_minutes("12:30"), time_to_minutes("14:00")),
                   (time_to_minutes("14:30"), time_to_minutes("15:00")),
                   (time_to_minutes("15:30"), time_to_minutes("16:00"))]
    }
    
    # Brian prefers to avoid Monday, so we check days in order: Tue, Wed, Thu, Fri, Mon
    days_order = ["Tuesday", "Wednesday", "Thursday", "Friday", "Monday"]
    
    result = find_earliest_meeting(brian_busy, julia_busy, days_order, 60)
    
    if result:
        day, start_min, end_min = result
        print(f"{day}")
        print(f"{minutes_to_time(start_min)}:{minutes_to_time(end_min)}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()