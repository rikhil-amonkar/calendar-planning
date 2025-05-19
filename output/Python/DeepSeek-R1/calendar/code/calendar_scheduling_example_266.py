def find_meeting_time():
    work_hours = (9 * 60, 17 * 60)
    participants = {
        'Joe': [(570, 600), (630, 660)],
        'Keith': [(690, 720), (900, 930)],
        'Patricia': [(540, 570), (780, 810)],
        'Nancy': [(540, 660), (690, 990)],
        'Pamela': [(540, 600), (630, 660), (690, 750), (780, 840), (870, 900), (930, 960), (990, 1020)]
    }

    for start in range(work_hours[0], work_hours[1] - 30 + 1):
        end = start + 30
        available = True
        for busy in participants.values():
            for s, e in busy:
                if not (end <= s or start >= e):
                    available = False
                    break
            if not available:
                break
        if available:
            return f"Monday:{start//60:02d}:{start%60:02d}:{end//60:02d}:{end%60:02d}"
    return "No time found"

print(find_meeting_time())