def time_to_minutes(hour, minute):
    return hour * 60 + minute

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Work hours
    work_start = time_to_minutes(9, 0)
    work_end = time_to_minutes(17, 0)
    duration = 30  # minutes
    
    # Busy times for each person (in minutes since midnight)
    # Format: (start_minute, end_minute)
    busy = {
        "Natalie": [],
        "David": [(time_to_minutes(11, 30), time_to_minutes(12, 0)),
                  (time_to_minutes(14, 30), time_to_minutes(15, 0))],
        "Douglas": [(time_to_minutes(9, 30), time_to_minutes(10, 0)),
                    (time_to_minutes(11, 30), time_to_minutes(12, 0)),
                    (time_to_minutes(13, 0), time_to_minutes(13, 30)),
                    (time_to_minutes(14, 30), time_to_minutes(15, 0))],
        "Ralph": [(time_to_minutes(9, 0), time_to_minutes(9, 30)),
                  (time_to_minutes(10, 0), time_to_minutes(11, 0)),
                  (time_to_minutes(11, 30), time_to_minutes(12, 30)),
                  (time_to_minutes(13, 30), time_to_minutes(15, 0)),
                  (time_to_minutes(15, 30), time_to_minutes(16, 0)),
                  (time_to_minutes(16, 30), time_to_minutes(17, 0))],
        "Jordan": [(time_to_minutes(9, 0), time_to_minutes(10, 0)),
                   (time_to_minutes(12, 0), time_to_minutes(12, 30)),
                   (time_to_minutes(13, 0), time_to_minutes(13, 30)),
                   (time_to_minutes(14, 30), time_to_minutes(15, 0)),
                   (time_to_minutes(15, 30), time_to_minutes(17, 0))]
    }
    
    # David's preference: not before 14:00
    david_pref_start = time_to_minutes(14, 0)
    
    # Check every possible start time in work hours
    for start in range(work_start, work_end - duration + 1, 30):
        end = start + duration
        # Check David's preference
        if start < david_pref_start:
            continue
        # Check if all are free
        ok = True
        for person, busy_slots in busy.items():
            for bs, be in busy_slots:
                if not (end <= bs or start >= be):
                    # Overlap with busy time
                    ok = False
                    break
            if not ok:
                break
        if ok:
            print(f"Monday {minutes_to_time(start)}:{minutes_to_time(end)}")
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()