from z3 import *

def solve_meeting_schedule():
    # Create the solver
    s = Solver()

    # Define the possible days (Monday=0, Tuesday=1, Wednesday=2)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define the start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    s.add(start_time >= 540, start_time <= 1020 - 30)  # 17:00 is 1020 minutes, meeting is 30 mins

    # Calculate end time (exactly 30 minutes after start)
    end_time = start_time + 30

    # Susan's blocked times in minutes from 9:00
    susan_blocked = {
        0: [(750, 780), (810, 840)],   # Monday
        1: [(810, 840)],                # Tuesday
        2: [(570, 630), (900, 930), (990, 1020)]  # Wednesday
    }

    # Sandra's blocked times in minutes from 9:00
    sandra_blocked = {
        0: [(540, 780), (840, 900), (1020, 1050)],  # Monday
        1: [(540, 570), (690, 780), (810, 870), (840, 870), (960, 1020)],  # Tuesday
        2: [(540, 750), (780, 810), (840, 1020)]  # Wednesday
    }

    # Susan prefers not to meet on Tuesday (day=1)
    s.add(day != 1)

    # Sandra cannot meet on Monday after 16:00 (day=0 and end_time <= 1020)
    s.add(Implies(day == 0, end_time <= 1020))

    # Function to add no-overlap constraints
    def add_no_overlap_constraints(day_num, blocked_times):
        for (block_start, block_end) in blocked_times:
            s.add(Not(And(day == day_num,
                         start_time < block_end,
                         end_time > block_start)))

    # Add constraints for Susan's availability
    for day_num, blocks in susan_blocked.items():
        add_no_overlap_constraints(day_num, blocks)

    # Add constraints for Sandra's availability
    for day_num, blocks in sandra_blocked.items():
        add_no_overlap_constraints(day_num, blocks)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        end_val = start_val + 30

        # Convert day and time to readable format
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        start_hour = start_val // 60
        start_min = start_val % 60
        end_hour = end_val // 60
        end_min = end_val % 60

        # Format the output
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

solve_meeting_schedule()