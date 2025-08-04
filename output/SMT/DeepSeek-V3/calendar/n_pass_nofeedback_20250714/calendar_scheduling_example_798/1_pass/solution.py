from z3 import *

def solve_scheduling():
    # Create the solver
    solver = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30)
    end_time = Int('end_time')
    
    # Meeting duration is 30 minutes
    solver.add(end_time == start_time + 30)
    
    # Meeting must be within work hours (9:00-17:00)
    solver.add(start_time >= 0)
    solver.add(end_time <= 8 * 60)  # 8 hours * 60 minutes = 480 minutes (from 9:00 to 17:00)
    
    # Define the blocked times for each person on each day
    # Nancy's blocked times:
    nancy_blocked = {
        0: [(10*60 - 9*60, 10*60 + 30 - 9*60),  # Monday 10:00-10:30 (60-90)
            (11*60 + 30 - 9*60, 12*60 + 30 - 9*60),  # 11:30-12:30 (150-210)
            (13*60 + 30 - 9*60, 14*60 - 9*60),  # 13:30-14:00 (270-300)
            (14*60 + 30 - 9*60, 15*60 + 30 - 9*60),  # 14:30-15:30 (330-390)
            (16*60 - 9*60, 17*60 - 9*60)],  # 16:00-17:00 (420-480)
        1: [(9*60 + 30 - 9*60, 10*60 + 30 - 9*60),  # Tuesday 9:30-10:30 (30-90)
            (11*60 - 9*60, 11*60 + 30 - 9*60),  # 11:00-11:30 (120-150)
            (12*60 - 9*60, 12*60 + 30 - 9*60),  # 12:00-12:30 (180-210)
            (13*60 - 9*60, 13*60 + 30 - 9*60),  # 13:00-13:30 (240-270)
            (15*60 + 30 - 9*60, 16*60 - 9*60)],  # 15:30-16:00 (390-420)
        2: [(10*60 - 9*60, 11*60 + 30 - 9*60),  # Wednesday 10:00-11:30 (60-150)
            (13*60 + 30 - 9*60, 16*60 - 9*60)]  # 13:30-16:00 (270-420)
    }
    
    # Jose's blocked times:
    jose_blocked = {
        0: [(9*60 - 9*60, 17*60 - 9*60)],  # Monday 9:00-17:00 (0-480)
        1: [(9*60 - 9*60, 17*60 - 9*60)],  # Tuesday 9:00-17:00 (0-480)
        2: [(9*60 - 9*60, 9*60 + 30 - 9*60),  # Wednesday 9:00-9:30 (0-30)
            (10*60 - 9*60, 12*60 + 30 - 9*60),  # 10:00-12:30 (60-210)
            (13*60 + 30 - 9*60, 14*60 + 30 - 9*60),  # 13:30-14:30 (270-330)
            (15*60 - 9*60, 17*60 - 9*60)]  # 15:00-17:00 (360-480)
    }
    
    # Constraints for each possible day
    day_constraints = []
    
    for d in [0, 1, 2]:
        # Nancy's availability on day d
        nancy_available = True
        for (block_start, block_end) in nancy_blocked[d]:
            # The meeting must not overlap with any blocked interval
            nancy_available = And(nancy_available,
                                  Or(end_time <= block_start, start_time >= block_end))
        
        # Jose's availability on day d
        jose_available = True
        for (block_start, block_end) in jose_blocked[d]:
            jose_available = And(jose_available,
                                Or(end_time <= block_start, start_time >= block_end))
        
        # If day is d, both must be available
        day_constraints.append(And(day == d, nancy_available, jose_available))
    
    solver.add(Or(day_constraints[0], day_constraints[1], day_constraints[2]))
    
    # Optimize for the earliest start time
    opt = Optimize()
    opt.add(solver.assertions())
    opt.minimize(start_time)
    
    if opt.check() == sat:
        model = opt.model()
        d = model[day].as_long()
        s = model[start_time].as_long()
        e = model[end_time].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday"]
        selected_day = days[d]
        
        # Convert start_time and end_time back to HH:MM format
        start_hour = 9 + s // 60
        start_minute = s % 60
        end_hour = 9 + e // 60
        end_minute = e % 60
        
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print(f"Day: {selected_day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()