from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 9:00 (540 in 24-hour format)
    end_time = Int('end_time')

    # Constraints for day
    s.add(day >= 0, day <= 3)  # Monday to Thursday

    # Meeting duration is 1 hour (60 minutes)
    s.add(end_time == start_time + 60)

    # Work hours are 9:00 to 17:00 (540 to 1020 minutes in 24-hour format)
    s.add(start_time >= 0)  # 9:00 is 0 minutes from 9:00
    s.add(end_time <= 480)   # 17:00 is 480 minutes from 9:00 (since 17:00 - 9:00 = 8 hours = 480 minutes)

    # Megan's busy times (converted to minutes from 9:00)
    megan_busy = {
        0: [(240, 270), (300, 390)],  # Monday 13:00-13:30, 14:00-15:30
        1: [(0, 30), (180, 210), (420, 480)],  # Tuesday 9:00-9:30, 12:00-12:30, 16:00-17:00
        2: [(30, 60), (90, 150), (210, 300), (420, 450)],  # Wednesday 9:30-10:00, 10:30-11:30, 12:30-14:00, 16:00-16:30
        3: [(270, 330), (360, 390)]  # Thursday 13:30-14:30, 15:00-15:30
    }

    # Daniel's busy times
    daniel_busy = {
        0: [(60, 150), (210, 360)],  # Monday 10:00-11:30, 12:30-15:00
        1: [(0, 60), (90, 480)],  # Tuesday 9:00-10:00, 10:30-17:00
        2: [(0, 60), (90, 150), (180, 480)],  # Wednesday 9:00-10:00, 10:30-11:30, 12:00-17:00
        3: [(0, 180), (210, 330), (360, 390), (420, 480)]  # Thursday 9:00-12:00, 12:30-14:30, 15:00-15:30, 16:00-17:00
    }

    # Function to add no-overlap constraints
    def add_no_overlap_constraints(day_var, start, end, busy_slots):
        for d in busy_slots:
            for (busy_start, busy_end) in busy_slots[d]:
                s.add(Not(And(day_var == d,
                              start < busy_end,
                              end > busy_start)))
    
    add_no_overlap_constraints(day, start_time, end_time, megan_busy)
    add_no_overlap_constraints(day, start_time, end_time, daniel_busy)

    # Find the earliest possible time: prioritize earlier days, then earlier start times
    # We'll use optimization to find the minimal day and start_time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(day * 10000 + start_time)  # day is higher priority

    if opt.check() == sat:
        model = opt.model()
        d = model[day].as_long()
        st = model[start_time].as_long()
        et = model[end_time].as_long()

        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        selected_day = days[d]
        
        # Convert start_time and end_time back to HH:MM format
        start_hour = 9 + st // 60
        start_min = st % 60
        end_hour = 9 + et // 60
        end_min = et % 60

        start_time_str = f"{start_hour:02d}:{start_min:02d}"
        end_time_str = f"{end_hour:02d}:{end_min:02d}"

        print("SOLUTION:")
        print(f"Day: {selected_day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()