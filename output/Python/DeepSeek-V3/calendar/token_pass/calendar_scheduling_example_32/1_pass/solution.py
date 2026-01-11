def schedule_meeting():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30

    # Busy times in minutes since midnight
    emily_busy = [(10*60, 10*60+30), (11*60+30, 12*60+30), (14*60, 15*60), (16*60, 16*60+30)]
    melissa_busy = [(9*60+30, 10*60), (14*60+30, 15*60)]
    frank_busy = [(10*60, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60), (13*60+30, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)]

    # Frank's extra constraint: not after 9:30
    frank_constraint_end = 9 * 60 + 30

    # Combine constraints: meeting must end by min(work_end, frank_constraint_end)
    latest_allowed_end = min(work_end, frank_constraint_end)

    # Check each possible start time from work_start to latest_allowed_end - duration
    for start in range(work_start, latest_allowed_end - duration + 1, 5):  # step 5 minutes for precision
        end = start + duration

        # Check Emily
        emily_free = all(not (start < busy_end and end > busy_start) for busy_start, busy_end in emily_busy)
        if not emily_free:
            continue

        # Check Melissa
        melissa_free = all(not (start < busy_end and end > busy_start) for busy_start, busy_end in melissa_busy)
        if not melissa_free:
            continue

        # Check Frank
        frank_free = all(not (start < busy_end and end > busy_start) for busy_start, busy_end in frank_busy)
        if not frank_free:
            continue

        # Format output
        def fmt(m):
            return f"{m//60:02d}:{m%60:02d}"
        print(f"Monday {fmt(start)}:{fmt(end)}")
        return

    print("No suitable time found")

if __name__ == "__main__":
    schedule_meeting()