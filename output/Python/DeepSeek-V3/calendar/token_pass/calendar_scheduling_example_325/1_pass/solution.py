def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    # Busy times in minutes from 0:00, we'll adjust to minutes from 9:00 later
    # But easier: define busy intervals in absolute minutes from midnight, then subtract work_start
    # Let's define them in minutes from 9:00 directly:
    
    busy = {
        "Jose": [(120, 150), (210, 240)],
        "Keith": [(300, 330), (360, 390)],
        "Logan": [(0, 60), (180, 210), (360, 390)],
        "Megan": [(0, 90), (120, 180), (240, 270), (330, 450)],
        "Gary": [(0, 30), (60, 90), (150, 240), (270, 300), (330, 450)],
        "Bobby": [(120, 150), (180, 210), (240, 420)]
    }
    
    # Jose's extra constraint: meeting must end by 15:30
    jose_limit = time_to_minutes("15:30") - work_start  # 15:30 is 6.5h after 9:00 → 390 minutes from 9:00
    
    # Check all possible start times from work_start to work_end - duration, in steps of 5 minutes for precision
    step = 5
    for start in range(0, work_end - work_start - duration + 1, step):
        end = start + duration
        if end > jose_limit:  # Jose's constraint
            continue
        
        ok = True
        for person, intervals in busy.items():
            for b_start, b_end in intervals:
                if not (end <= b_start or start >= b_end):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            # Found slot
            start_abs = work_start + start
            end_abs = start_abs + duration
            print(f"Monday {minutes_to_time(start_abs)}:{minutes_to_time(end_abs)[3:5]}")
            return
    
    print("No suitable slot found")

if __name__ == "__main__":
    main()