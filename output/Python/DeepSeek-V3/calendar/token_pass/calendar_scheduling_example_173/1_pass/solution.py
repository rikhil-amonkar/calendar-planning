def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to 'HH:MM'."""
    return f"{m // 60:02d}:{m % 60:02d}"

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    # Busy intervals in minutes from 00:00
    busy = {
        "Jacqueline": [
            ("09:00", "09:30"),
            ("11:00", "11:30"),
            ("12:30", "13:00"),
            ("15:30", "16:00"),
        ],
        "Harold": [
            ("10:00", "10:30"),
            ("13:00", "13:30"),
            ("15:00", "17:00"),
        ],
        "Arthur": [
            ("09:00", "09:30"),
            ("10:00", "12:30"),
            ("14:30", "15:00"),
            ("15:30", "17:00"),
        ],
        "Kelly": [
            ("09:00", "09:30"),
            ("10:00", "11:00"),
            ("11:30", "12:30"),
            ("14:00", "15:00"),
            ("15:30", "16:00"),
        ],
    }
    
    # Convert all to minutes since midnight
    busy_min = {}
    for person, intervals in busy.items():
        busy_min[person] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
    
    # Harold's constraint: meeting must end by 13:00
    harold_limit = time_to_minutes("13:00")
    
    # Check every possible start time from work_start to work_end - duration, step 1 minute
    # (or step 30 minutes for efficiency, but step 1 to be safe)
    for start in range(work_start, work_end - duration + 1):
        end = start + duration
        
        # Check Harold's time preference
        if end > harold_limit:
            continue
        
        # Check if all are free
        ok = True
        for person, intervals in busy_min.items():
            for bs, be in intervals:
                if not (end <= bs or start >= be):
                    ok = False
                    break
            if not ok:
                break
        
        if ok:
            print(f"Monday:{minutes_to_time(start)}:{minutes_to_time(end)}")
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()