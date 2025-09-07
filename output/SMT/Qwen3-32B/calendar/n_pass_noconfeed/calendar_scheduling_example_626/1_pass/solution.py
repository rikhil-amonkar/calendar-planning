from z3 import *

def schedule_meeting():
    # Define existing meetings for each day and participant
    # Monday Patricia
    p_mon_meetings = [
        (600, 630), (690, 720), (780, 810), (870, 930), (960, 990)
    ]
    # Monday Jesse
    j_mon_meetings = [(540, 1020)]
    
    # Tuesday Patricia
    p_tue_meetings = [
        (600, 630), (660, 720), (840, 960), (990, 1020)
    ]
    # Tuesday Jesse
    j_tue_meetings = [
        (660, 690), (720, 750), (780, 840), (870, 900), (930, 1020)
    ]
    
    # Check Monday
    s_mon = Solver()
    start_mon = Int('start_mon')
    s_mon.add(540 <= start_mon, start_mon + 60 <= 1020)
    for s_p, e_p in p_mon_meetings:
        s_mon.add(Or(start_mon + 60 <= s_p, start_mon >= e_p))
    for s_j, e_j in j_mon_meetings:
        s_mon.add(Or(start_mon + 60 <= s_j, start_mon >= e_j))
    if s_mon.check() == sat:
        m = s_mon.model()
        start_time = m[start_mon].as_long()
        day = "Monday"
    else:
        # Check Tuesday
        s_tue = Solver()
        start_tue = Int('start_tue')
        s_tue.add(540 <= start_tue, start_tue + 60 <= 1020)
        for s_p, e_p in p_tue_meetings:
            s_tue.add(Or(start_tue + 60 <= s_p, start_tue >= e_p))
        for s_j, e_j in j_tue_meetings:
            s_tue.add(Or(start_tue + 60 <= s_j, start_tue >= e_j))
        if s_tue.check() == sat:
            m = s_tue.model()
            start_time = m[start_tue].as_long()
            day = "Tuesday"
        else:
            print("No solution found")
            return
    
    # Format the output
    start_h = start_time // 60
    start_m = start_time % 60
    end_time = start_time + 60
    end_h = end_time // 60
    end_m = end_time % 60
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(f"{time_str} {day}")

schedule_meeting()