from z3 import *

def main():
    # Initialize the solver
    s = Int('s')
    solver = Solver()
    
    # Meeting duration is 30 minutes, workday is 9:00 (0 min) to 17:00 (480 min)
    solver.add(s >= 0)
    solver.add(s <= 450)  # 450 + 30 = 480 (17:00)
    
    # Bradley's busy intervals (in minutes from 9:00)
    bradley_busy = [(30, 60), (210, 240), (270, 300), (390, 420)]
    for start, end in bradley_busy:
        solver.add(Or(s + 30 <= start, s >= end))
    
    # Teresa's busy intervals
    teresa_busy = [(90, 120), (180, 210), (240, 270), (330, 360)]
    for start, end in teresa_busy:
        solver.add(Or(s + 30 <= start, s >= end))
    
    # Elizabeth's busy intervals
    elizabeth_busy = [(0, 30), (90, 150), (240, 270), (330, 360), (390, 480)]
    for start, end in elizabeth_busy:
        solver.add(Or(s + 30 <= start, s >= end))
    
    # Christian's busy intervals
    christian_busy = [(0, 30), (90, 480)]
    for start, end in christian_busy:
        solver.add(Or(s + 30 <= start, s >= end))
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        start_minutes = m[s].as_long()
        
        # Convert start_minutes to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday, {start_time}, {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()