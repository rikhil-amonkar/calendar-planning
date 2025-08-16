from z3 import Optimize, Int, Or, And

def hm(h, m):
    return h * 60 + m

def format_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    day = "Monday"
    meeting_duration = 30  # in minutes

    # Work hours
    work_start = hm(9, 0)
    work_end = hm(17, 0)

    # Blocked intervals for each participant: [start, end) in minutes since midnight
    schedules = {
        "Doris": [
            (hm(9, 0), hm(11, 0)),
            (hm(13, 30), hm(14, 0)),
            (hm(16, 0), hm(16, 30)),
        ],
        "Theresa": [
            (hm(10, 0), hm(12, 0)),
        ],
        "Christian": [
            # No blocks
        ],
        "Terry": [
            (hm(9, 30), hm(10, 0)),
            (hm(11, 30), hm(12, 0)),
            (hm(12, 30), hm(13, 0)),
            (hm(13, 30), hm(14, 0)),
            (hm(14, 30), hm(15, 0)),
            (hm(15, 30), hm(17, 0)),
        ],
        "Carolyn": [
            (hm(9, 0), hm(10, 30)),
            (hm(11, 0), hm(11, 30)),
            (hm(12, 0), hm(13, 0)),
            (hm(13, 30), hm(14, 30)),
            (hm(15, 0), hm(17, 0)),
        ],
        "Kyle": [
            (hm(9, 0), hm(9, 30)),
            (hm(11, 30), hm(12, 0)),
            (hm(12, 30), hm(13, 0)),
            (hm(14, 30), hm(17, 0)),
        ],
    }

    # Z3 variables
    start = Int("start")

    opt = Optimize()

    # Meeting within work hours
    opt.add(start >= work_start)
    opt.add(start + meeting_duration <= work_end)

    # Optional: restrict starts to 30-minute increments
    opt.add(start % 30 == 0)

    # No overlap with any participant's blocked intervals
    for person, blocks in schedules.items():
        for b_start, b_end in blocks:
            # Either the meeting ends before the block starts, or starts after the block ends
            opt.add(Or(start + meeting_duration <= b_start, start >= b_end))

    # Optionally, choose the earliest valid time
    opt.minimize(start)

    if opt.check().r == 1:  # sat
        model = opt.model()
        s_val = model[start].as_long()
        e_val = s_val + meeting_duration

        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {format_time(s_val)}")
        print(f"End Time: {format_time(e_val)}")
    else:
        # The problem statement guarantees a solution exists, but handle just in case
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: 00:00")
        print("End Time: 00:30")

if __name__ == "__main__":
    schedule_meeting()