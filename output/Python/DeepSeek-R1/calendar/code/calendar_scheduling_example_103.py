def find_meeting_time():
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30

    # Convert blocked times to minutes since midnight
    blocked = {
        'Diane': [(570, 600), (870, 900)],
        'Jack': [(810, 840), (870, 900)],
        'Eugene': [(540, 600), (630, 690), (720, 870), (900, 990)],
        'Patricia': [(570, 630), (660, 720), (750, 840), (900, 990)]
    }

    # Check every possible 30-minute slot
    for start in range(work_start, work_end - duration + 1):
        end = start + duration
        # Check if slot is fully within work hours
        if end > work_end:
            continue
        # Check all participants' availability
        available = True
        for person, blocks in blocked.items():
            for s, e in blocks:
                if not (end <= s or start >= e):
                    available = False
                    break
            if not available:
                break
        if available:
            # Convert back to HH:MM format
            def to_time(mins):
                return f"{mins//60:02d}:{mins%60:02d}"
            return f"Monday {to_time(start)}-{to_time(end)}"
    return "No time found"

print(find_meeting_time())