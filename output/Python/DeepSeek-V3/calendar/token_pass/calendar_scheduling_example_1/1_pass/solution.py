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
    
    # Blocked times in minutes from 0:00, we'll adjust to work_start offset
    # Actually easier: work from 9:00 as 0 offset
    # So convert given times to minutes since 9:00
    def since9(t):
        return time_to_minutes(t) - work_start
    
    raymond_blocked = [
        (since9("9:00"), since9("9:30")),
        (since9("11:30"), since9("12:00")),
        (since9("13:00"), since9("13:30")),
        (since9("15:00"), since9("15:30"))
    ]
    billy_blocked = [
        (since9("10:00"), since9("10:30")),
        (since9("12:00"), since9("13:00")),
        (since9("16:30"), since9("17:00"))
    ]
    donald_blocked = [
        (since9("9:00"), since9("9:30")),
        (since9("10:00"), since9("11:00")),
        (since9("12:00"), since9("13:00")),
        (since9("14:00"), since9("14:30")),
        (since9("16:00"), since9("17:00"))
    ]
    
    # Billy's preference: avoid after 15:00 means start < since9("15:00") = 360
    pref_max_start = since9("15:00")
    
    # Check every possible start from work_start to work_end - duration
    for start in range(0, work_end - work_start - duration + 1):
        end = start + duration
        # Check if slot overlaps with any blocked time for any person
        conflict = False
        for b_start, b_end in raymond_blocked:
            if not (end <= b_start or start >= b_end):
                conflict = True
                break
        if conflict:
            continue
        for b_start, b_end in billy_blocked:
            if not (end <= b_start or start >= b_end):
                conflict = True
                break
        if conflict:
            continue
        for b_start, b_end in donald_blocked:
            if not (end <= b_start or start >= b_end):
                conflict = True
                break
        if conflict:
            continue
        # Check Billy's preference
        if start >= pref_max_start:
            continue
        # Found a slot
        start_abs = work_start + start
        end_abs = start_abs + duration
        print(f"Monday {minutes_to_time(start_abs)}:{minutes_to_time(end_abs)}")
        return
    
    print("No suitable slot found")

if __name__ == "__main__":
    main()