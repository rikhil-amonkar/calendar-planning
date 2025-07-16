from z3 import *

def solve_scheduling():
    s = Solver()
    
    start_time = Int('start_time')
    duration = 30
    end_time = start_time + duration
    
    # Work hours 9:00-17:00 (0 to 480 minutes)
    s.add(start_time >= 0)
    s.add(end_time <= 480)
    
    # Megan's busy intervals: 0-30, 60-120, 180-210
    s.add(Or(start_time >= 30, end_time <= 0))
    s.add(Or(start_time >= 120, end_time <= 60))
    s.add(Or(start_time >= 210, end_time <= 180))
    
    # Christine's busy intervals: 0-30, 150-180, 240-300, 390-450
    s.add(Or(start_time >= 30, end_time <= 0))
    s.add(Or(start_time >= 180, end_time <= 150))
    s.add(Or(start_time >= 300, end_time <= 240))
    s.add(Or(start_time >= 450, end_time <= 390))
    
    # Gabriel: no constraints
    
    # Sara's busy intervals: 150-180, 270-300
    s.add(Or(start_time >= 180, end_time <= 150))
    s.add(Or(start_time >= 300, end_time <= 270))
    
    # Bruce's busy intervals: 30-60, 90-180, 210-300, 390-450
    s.add(Or(start_time >= 60, end_time <= 30))
    s.add(Or(start_time >= 180, end_time <= 90))
    s.add(Or(start_time >= 300, end_time <= 210))
    s.add(Or(start_time >= 450, end_time <= 390))
    
    # Kathryn's busy intervals: 60-390, 420-450
    s.add(Or(start_time >= 390, end_time <= 60))
    s.add(Or(start_time >= 450, end_time <= 420))
    
    # Billy's busy intervals: 0-30, 120-150, 180-300, 270-330
    s.add(Or(start_time >= 30, end_time <= 0))
    s.add(Or(start_time >= 150, end_time <= 120))
    s.add(Or(start_time >= 300, end_time <= 180))
    s.add(Or(start_time >= 330, end_time <= 270))
    
    if s.check() == sat:
        model = s.model()
        start = model[start_time].as_long()
        
        hours = 9 + start // 60
        minutes = start % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end = start + duration
        end_hours = 9 + end // 60
        end_minutes = end % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_scheduling()