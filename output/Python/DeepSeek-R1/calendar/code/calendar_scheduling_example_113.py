def find_meeting_time():
    work_hours = (9 * 60, 17 * 60)
    participants = {
        'Bradley': [(570, 600), (750, 780), (810, 840), (930, 960)],
        'Teresa': [(630, 660), (720, 750), (780, 810), (870, 900)],
        'Elizabeth': [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)],
        'Christian': [(540, 570), (630, 1020)]
    }

    for start in range(work_hours[0], work_hours[1] - 30 + 1):
        end = start + 30
        conflict = False
        for busy in participants.values():
            for s, e in busy:
                if not (end <= s or start >= e):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            return f"Monday {start_hr:02}:{start_min:02}:{end_hr:02}:{end_min:02}"
    return "No time found"

print(find_meeting_time())