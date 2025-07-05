from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define start and end time variables in minutes since midnight
    start = Int('start')
    end = Int('end')
    
    # Add constraints for meeting duration and work hours
    solver.add(start >= work_start)
    solver.add(end <= work_end)
    solver.add(end == start + duration)
    
    # Samuel's blocked times in minutes since midnight
    samuel_blocked = [
        (540, 630),    # 9:00-10:30
        (690, 720),     # 11:30-12:00
        (780, 810),     # 13:00-13:30
        (840, 960),     # 14:00-16:00
        (990, 1020)     # 16:30-17:00
    ]
    
    # Add constraints for Samuel's availability
    for block_start, block_end in samuel_blocked:
        solver.add(Or(end <= block_start, start >= block_end))
    
    # Andrew and Grace have no meetings, so no additional constraints
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_min = model[start].as_long()
        end_min = model[end].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_hh = end_min // 60
        end_mm = end_min % 60
        
        # Format the output
        solution = (
            f"SOLUTION:\n"
            f"Day: Monday\n"
            f"Start Time: {start_hh:02d}:{start_mm:02d}\n"
            f"End Time: {end_hh:02d}:{end_mm:02d}"
        )
        print(solution)
    else:
        print("No solution found")

solve_scheduling()