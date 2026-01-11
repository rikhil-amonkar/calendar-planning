def schedule_meeting():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 60        # 1 hour in minutes

    # Blocked times in minutes since midnight
    blocked = {
        "Olivia": [(12*60+30, 13*60+30), (14*60+30, 15*60), (16*60+30, 17*60)],
        "Virginia": [(9*60, 10*60), (11*60+30, 16*60), (16*60+30, 17*60)],
        "Paul": [(9*60, 9*60+30), (11*60, 11*60+30), (13*60, 14*60), (14*60+30, 16*60), (16*60+30, 17*60)],
        "Anna": []  # No meetings
    }

    # Check each minute slot from work_start to work_end - duration
    for start in range(work_start, work_end - duration + 1):
        end = start + duration
        ok = True
        for person, blocks in blocked.items():
            for b_start, b_end in blocks:
                # If overlap exists
                if not (end <= b_start or start >= b_end):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            # Convert back to HH:MM
            def fmt(m):
                h = m // 60
                mm = m % 60
                return f"{h:02d}:{mm:02d}"
            print(f"Monday {fmt(start)}:{fmt(end)}")
            return

    print("No suitable time found")

if __name__ == "__main__":
    schedule_meeting()