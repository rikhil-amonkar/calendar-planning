def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30
    day = "Monday"

    # Convert schedules to minutes since midnight
    schedules = {
        "Shirley": [(630, 660), (720, 750)],
        "Jacob": [(540, 570), (600, 630), (660, 690), (750, 810), (870, 900)],
        "Stephen": [(690, 720), (750, 780)],
        "Margaret": [(540, 570), (630, 750), (780, 810), (900, 930), (990, 1020)],
        "Mason": [(540, 600), (630, 660), (690, 750), (780, 810), (840, 870), (990, 1020)]
    }

    # Margaret's time constraint
    margaret_min = 14 * 60 + 30  # 14:30

    # Check every possible 30-minute slot between work hours
    for start in range(work_start, work_end - meeting_duration + 1):
        end = start + meeting_duration
        # Check Margaret's preference
        if start < margaret_min:
            continue
        # Check all participants' availability
        conflict = False
        for person, busy in schedules.items():
            for s, e in busy:
                if not (end <= s or start >= e):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            # Convert back to HH:MM format
            def to_time(minutes):
                return f"{minutes//60:02}:{minutes%60:02}"
            return f"{day} {to_time(start)}:{to_time(end)}"
    return None

result = find_meeting_time()
print(result)