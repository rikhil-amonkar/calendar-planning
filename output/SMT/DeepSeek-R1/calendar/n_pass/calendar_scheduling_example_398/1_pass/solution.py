from z3 import *

def main():
    # Initialize Z3 solver
    s = Int('start_time')
    solver = Solver()
    
    # Meeting duration is 30 minutes, and must be within 9:00 (0 min) to 17:00 (480 min)
    solver.add(s >= 0, s <= 450)  # 450 because 450+30=480 (17:00)
    
    # Blocked intervals for each participant in minutes (start inclusive, end exclusive)
    doris = [(0, 120), (270, 300), (420, 450)]
    theresa = [(60, 120)]
    # Christian has no blocked intervals
    terry = [(30, 60), (150, 180), (210, 240), (270, 300), (330, 360), (390, 480)]
    carolyn = [(0, 90), (120, 150), (180, 240), (270, 330), (360, 480)]
    kyle = [(0, 30), (150, 180), (210, 240), (330, 480)]
    
    # Add constraints for Doris
    for (start_block, end_block) in doris:
        solver.add(Or(s + 30 <= start_block, s >= end_block))
    
    # Add constraints for Theresa
    for (start_block, end_block) in theresa:
        solver.add(Or(s + 30 <= start_block, s >= end_block))
    
    # Add constraints for Terry
    for (start_block, end_block) in terry:
        solver.add(Or(s + 30 <= start_block, s >= end_block))
    
    # Add constraints for Carolyn
    for (start_block, end_block) in carolyn:
        solver.add(Or(s + 30 <= start_block, s >= end_block))
    
    # Add constraints for Kyle
    for (start_block, end_block) in kyle:
        solver.add(Or(s + 30 <= start_block, s >= end_block))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        
        # Convert start_minutes to time string
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{9 + hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        end_hours = end_minutes // 60
        end_minutes %= 60
        end_time_str = f"{9 + end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()