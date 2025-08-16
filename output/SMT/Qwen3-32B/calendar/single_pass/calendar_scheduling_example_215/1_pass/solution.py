from z3 import *

def schedule_meeting():
    opt = Optimize()
    S = Int('S')
    opt.add(S >= 540)  # 9:00 AM in minutes
    opt.add(S + 30 <= 1020)  # 5:00 PM in minutes

    # Define all busy intervals for participants
    busy_intervals = [
        # Cynthia's busy intervals
        (570, 630), (690, 720), (780, 810), (900, 960),
        # Lauren's busy intervals
        (540, 570), (630, 660), (690, 720), (780, 810), (840, 870), (900, 930), (960, 1020),
        # Robert's busy intervals
        (630, 660), (690, 720), (750, 810), (840, 960)
    ]

    # Add constraints for each busy interval
    for b_start, b_end in busy_intervals:
        opt.add(Or(S + 30 <= b_start, S >= b_end))

    # Minimize the start time
    opt.minimize(S)

    if opt.check() == sat:
        m = opt.model()
        start_time = m.eval(S).as_long()
        end_time = start_time + 30

        # Convert minutes to HH:MM format
        start_hh = start_time // 60
        start_mm = start_time % 60
        end_hh = end_time // 60
        end_mm = end_time % 60

        return f"SOLUTION:\nDay: Monday\nStart Time: {start_hh:02d}:{start_mm:02d}\nEnd Time: {end_hh:02d}:{end_mm:02d}"
    else:
        return "No solution found."

print(schedule_meeting())