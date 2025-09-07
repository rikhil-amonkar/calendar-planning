from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def add_busy_constraints(solver, busy_intervals, var):
    for start, end in busy_intervals:
        solver.add(Or(var >= end, var + 30 <= start))

def main():
    solver = Solver()
    S = Int('S')
    
    # Overall time constraints (9:00 to 17:00, 30-minute meeting)
    solver.add(S >= 540)  # 9:00 AM
    solver.add(S + 30 <= 1020)  # 5:00 PM
    
    # David's preference (after 14:00)
    solver.add(S >= 840)  # 2:00 PM
    
    # Busy intervals for each participant
    busy_david = [(690, 720), (870, 900)]  # 11:30-12:00, 14:30-15:00
    busy_douglas = [(570, 600), (690, 720), (780, 810), (870, 900)]  # 9:30-10:00, etc.
    busy_ralph = [(540, 570), (600, 660), (690, 750), (810, 900), (930, 960), (990, 1020)]
    busy_jordan = [(540, 600), (720, 750), (780, 810), (870, 900), (930, 1020)]
    
    # Add constraints for each person's busy times
    add_busy_constraints(solver, busy_david, S)
    add_busy_constraints(solver, busy_douglas, S)
    add_busy_constraints(solver, busy_ralph, S)
    add_busy_constraints(solver, busy_jordan, S)
    
    if solver.check() == sat:
        model = solver.model()
        start_time = model[S].as_long()
        end_time = start_time + 30
        day = "Monday"
        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(end_time)
        print(f"{start_str}:{end_str} {day}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()