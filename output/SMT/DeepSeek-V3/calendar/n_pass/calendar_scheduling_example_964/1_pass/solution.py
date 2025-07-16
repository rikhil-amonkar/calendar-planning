from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()
    
    # Days: Monday (0), Tuesday (1), Wednesday (2), Thursday (3), Friday (4)
    day = Int('day')
    start_time_min = Int('start_time_min')  # in minutes since 00:00
    
    # Possible days: Monday (0), Tuesday (1), Friday (4) (Betty can't meet on Wednesday or Thursday)
    s.add(Or(day == 0, day == 1, day == 4))
    
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    
    # Work hours are 9:00 (540 mins) to 17:00 (1020 mins)
    s.add(start_time_min >= 540)
    s.add(start_time_min + duration <= 1020)
    
    # Betty's busy times per day
    betty_busy = {
        0: [(600, 630), (690, 750), (960, 990)],  # Monday 10:00-10:30, 11:30-12:30, 16:00-16:30
        1: [(570, 600), (630, 660), (720, 750), (810, 900), (990, 1020)],  # Tuesday 9:30-10:00, 10:30-11:00, 12:00-12:30, 13:30-15:00, 16:30-17:00
        4: [(540, 600), (690, 720), (750, 780), (870, 900)]  # Friday 9:00-10:00, 11:30-12:00, 12:30-13:00, 14:30-15:00
    }
    
    # Megan's busy times per day
    megan_busy = {
        0: [(540, 1020)],  # Monday all day
        1: [(540, 570), (600, 630), (720, 840), (900, 930), (960, 990)],  # Tuesday 9:00-9:30, 10:00-10:30, 12:00-14:00, 15:00-15:30, 16:00-16:30
        4: [(540, 1020)]  # Friday all day
    }
    
    # Function to add no-overlap constraints for a day
    def add_no_overlap_constraints(day_val, busy_slots):
        constraints = []
        meeting_start = start_time_min
        meeting_end = meeting_start + duration
        for (busy_start, busy_end) in busy_slots:
            constraints.append(Or(
                meeting_end <= busy_start,
                meeting_start >= busy_end
            ))
        return And(constraints)
    
    # Add constraints based on the selected day
    for d in [0, 1, 4]:
        # If day is d, then add the corresponding constraints
        s.add(Implies(day == d, add_no_overlap_constraints(d, betty_busy[d])))
        s.add(Implies(day == d, add_no_overlap_constraints(d, megan_busy[d])))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_min = m[start_time_min].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]
        
        # Convert start_min to HH:MM
        start_hour = start_min // 60
        start_minute = start_min % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_min = start_min + duration
        end_hour = end_min // 60
        end_minute = end_min % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

solve_scheduling()