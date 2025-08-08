def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def has_conflict(meeting_start, meeting_end, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Check if the meeting interval [meeting_start, meeting_end)
        # overlaps with the busy interval [busy_start, busy_end)
        if meeting_start < busy_end and meeting_end > busy_start:
            return True
    return False

# Schedules for each participant by day (times in minutes since midnight)
# Work hours are 9:00 (540 minutes) to 17:00 (1020 minutes)
schedules = {
    "Monday": {
        "Ronald": [(630, 660), (720, 750), (930, 960)],  # 10:30-11:00, 12:00-12:30, 15:30-16:00
        "Amber": [(540, 570), (600, 630), (690, 720), (750, 840), (870, 900), (930, 1020)]
                # 9:00-9:30, 10:00-10:30, 11:30-12:00, 12:30-14:00, 14:30-15:00, 15:30-17:00
    },
    "Tuesday": {
        "Ronald": [(540, 570), (720, 750), (930, 990)],  # 9:00-9:30, 12:00-12:30, 15:30-16:30
        "Amber": [(540, 570), (600, 690), (720, 750), (810, 930), (990, 1020)]
                # 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:30-15:30, 16:30-17:00
    },
    "Wednesday": {
        "Ronald": [(570, 630), (660, 720), (750, 780), (810, 840), (990, 1020)],
                # 9:30-10:30, 11:00-12:00, 12:30-13:00, 13:30-14:00, 16:30-17:00
        "Amber": [(540, 570), (600, 630), (660, 810), (900, 930)]
                # 9:00-9:30, 10:00-10:30, 11:00-13:30, 15:00-15:30
    }
}

meeting_duration = 30       # Duration in minutes
work_start = 540            # 9:00 in minutes
work_end = 1020             # 17:00 in minutes
days = ["Monday", "Tuesday", "Wednesday"]

found_slot = False

for day in days:
    # Iterate through possible start times (minute by minute)
    for start in range(work_start, work_end - meeting_duration + 1):
        end = start + meeting_duration
        conflict = False
        # Check each participant's busy intervals for the given day
        for person, busy in schedules[day].items():
            if has_conflict(start, end, busy):
                conflict = True
                break
        if not conflict:
            # Earliest available slot found; format and print the result.
            start_str = format_time(start)
            end_str = format_time(end)
            print(f"{day} {{{start_str}:{end_str}}}")
            found_slot = True
            break
    if found_slot:
        break