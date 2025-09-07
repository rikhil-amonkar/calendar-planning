from z3 import *

def schedule_meeting():
    # Define existing meetings for each day and participant
    # Monday
    p_mon_meetings = [(600, 630), (690, 720), (780, 810), (870, 930), (960, 990)]
    j_mon_meetings = [(540, 1020)]

    # Tuesday
    p_tue_meetings = [(600, 630), (660, 720), (840, 960), (990, 1020)]
    j_tue_meetings = [(660, 690), (720, 750), (780, 840), (870, 900), (930, 1020)]

    # Try to find a valid meeting time on Monday
    s_mon = Solver()
    start_mon = Int('start_mon')
    s_mon.add(540 <= start_mon, start_mon + 60 <= 1020)  # Within business hours
    for s, e in p_mon_meetings + j_mon_meetings:
        s_mon.add(Or(start_mon + 60 <= s, start_mon >= e))  # No overlap with existing meetings

    if s_mon.check() == sat:
        m = s_mon.model()
        start_time = m[start_mon].as_long()
        day = "Monday"
    else:
        # Try to find a valid meeting time on Tuesday
        s_tue = Solver()
        start_tue = Int('start_tue')
        s_tue.add(540 <= start_tue, start_tue + 60 <= 1020)  # Within business hours
        for s, e in p_tue_meetings + j_tue_meetings:
            s_tue.add(Or(start_tue + 60 <= s, start_tue >= e))  # No overlap with existing meetings

        if s_tue.check() == sat:
            m = s_tue.model()
            start_time = m[start_tue].as_long()
            day = "Tuesday"
        else:
            print("No solution found")
            return

    # Format the time in HH:MM:HH:MM format
    start_h, start_m = divmod(start_time, 60)
    end_time = start_time + 60
    end_h, end_m = divmod(end_time, 60)
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{time_str} {day}")

schedule_meeting()