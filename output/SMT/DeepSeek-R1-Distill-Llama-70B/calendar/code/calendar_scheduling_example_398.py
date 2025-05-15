import z3

def schedule_meeting():
    solver = z3.Solver()
    S = z3.Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020)
    # Meeting duration is 30 minutes, so latest start time is 1020 - 30 = 990 (16:30)
    solver.add(S >= 540)  # 9:00 AM
    solver.add(S <= 990)  # 16:30 to allow for 30-minute meeting

    # Blocked intervals for each participant in minutes since midnight
    blocked = {
        'Doris': [(540, 660), (810, 840), (960, 990)],
        'Theresa': [(600, 720)],
        'Terry': [(570, 600), (690, 720), (750, 780), (810, 840), (870, 900), (930, 1020)],
        'Carolyn': [(540, 630), (660, 690), (720, 780), (810, 870), (900, 1020)],
        'Kyle': [(540, 570), (690, 720), (750, 780), (870, 1020)]
    }

    # Add constraints for each blocked interval
    for person, intervals in blocked.items():
        for start_block, end_block in intervals:
            # Meeting ends before the blocked interval starts OR starts after the blocked interval ends
            solver.add(z3.Or(S >= end_block, S + 30 <= start_block))

    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        start = model[S].as_long()
        end = start + 30

        # Convert minutes to HH:MM format
        def to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        print(f"Day: Monday")
        print(f"Start time: {to_time(start)}")
        print(f"End time: {to_time(end)}")
    else:
        print("No solution found.")

schedule_meeting()