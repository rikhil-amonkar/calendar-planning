def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    # Busy intervals in minutes from midnight (but we'll compare relative to work hours)
    # Actually easier: keep as minutes from 0:00, then compare.
    # Let's keep all times in minutes from 0:00.
    
    # Adam
    adam_busy = [(time_to_minutes("14:00"), time_to_minutes("15:00"))]
    
    # John
    john_busy = [
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Stephanie
    steph_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Anna
    anna_busy = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    anna_pref_start = time_to_minutes("14:30")
    
    # Combine all schedules
    schedules = [adam_busy, john_busy, steph_busy, anna_busy]
    
    # Check every slot start from work_start to work_end - duration
    for start_min in range(work_start, work_end - duration + 1, 30):
        end_min = start_min + duration
        
        # Anna's preference
        if start_min < anna_pref_start:
            continue
        
        # Check if all are free
        conflict = False
        for busy_intervals in schedules:
            for busy_start, busy_end in busy_intervals:
                if not (end_min <= busy_start or start_min >= busy_end):
                    conflict = True
                    break
            if conflict:
                break
        
        if not conflict:
            print(f"Monday {minutes_to_time(start_min)}:{minutes_to_time(end_min)}")
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()