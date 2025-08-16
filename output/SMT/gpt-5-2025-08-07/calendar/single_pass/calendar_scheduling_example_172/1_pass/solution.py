from z3 import Optimize, Int, Or

def mins(h, m):
    return h * 60 + m

def schedule_meeting():
    # Work hours and meeting duration
    work_start = mins(9, 0)   # 09:00
    work_end = mins(17, 0)    # 17:00
    duration = 30             # 30 minutes

    # Create optimizer to get the earliest feasible time
    opt = Optimize()

    # Decision variables
    start = Int('start')
    end = Int('end')

    # Basic constraints: within work hours and fixed duration
    opt.add(end == start + duration)
    opt.add(start >= work_start, end <= work_end)

    # Busy schedules: intervals are [start, end) in minutes since midnight
    schedules = {
        "Patrick": [
            (mins(9, 0), mins(9, 30)),
            (mins(10, 0), mins(10, 30)),
            (mins(13, 30), mins(14, 0)),
            (mins(16, 0), mins(16, 30)),
        ],
        "Kayla": [
            (mins(12, 30), mins(13, 30)),
            (mins(15, 0), mins(15, 30)),
            (mins(16, 0), mins(16, 30)),
        ],
        "Carl": [
            (mins(10, 30), mins(11, 0)),
            (mins(12, 0), mins(12, 30)),
            (mins(13, 0), mins(13, 30)),
            (mins(14, 30), mins(17, 0)),
        ],
        "Christian": [
            (mins(9, 0), mins(12, 30)),
            (mins(13, 0), mins(14, 0)),
            (mins(14, 30), mins(17, 0)),
        ],
    }

    # Add non-overlap constraints for each participant's busy intervals
    for person, busy_list in schedules.items():
        for (b_start, b_end) in busy_list:
            opt.add(Or(end <= b_start, start >= b_end))

    # Optimize for earliest possible start time
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        start_val = model[start].as_long()
        end_val = model[end].as_long()

        def fmt(t):
            return f"{t // 60:02d}:{t % 60:02d}"

        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {fmt(start_val)}")
        print(f"End Time: {fmt(end_val)}")
    else:
        # According to the problem, a solution exists, but handle gracefully.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: 00:00")
        print("End Time: 00:30")

if __name__ == "__main__":
    schedule_meeting()