from z3 import *

def main():
    # Represent time in minutes from 9:00 (0 minutes = 9:00)
    start = Int('start')
    duration = 30  # Meeting duration in minutes
    
    # Work hours constraint: 9:00 to 17:00 (0 to 480 minutes)
    work_start = 0
    work_end = 480
    
    # Nicole's busy intervals in minutes from 9:00
    # 9:00-10:00 -> 0-60 minutes
    # 10:30-16:30 -> 90-450 minutes
    nicole_busy = [(0, 60), (90, 450)]
    
    # Constraints
    constraints = [
        start >= work_start,
        start + duration <= work_end
    ]
    
    # Add constraints for Nicole's busy times
    nicole_free = []
    current_start = work_start
    for busy_start, busy_end in nicole_busy:
        if current_start < busy_start:
            nicole_free.append((current_start, busy_start))
        current_start = busy_end
    if current_start < work_end:
        nicole_free.append((current_start, work_end))
    
    # The meeting must fit within one of Nicole's free intervals
    nicole_constraints = []
    for free_start, free_end in nicole_free:
        nicole_constraints.append(
            And(start >= free_start, start + duration <= free_end)
        )
    constraints.append(Or(nicole_constraints))
    
    # Nicole's preference: not before 16:00 (420 minutes from 9:00)
    preference = (start >= 420)
    
    # Use optimizer to maximize start time (prefer later times)
    opt = Optimize()
    for c in constraints:
        opt.add(c)
    opt.maximize(start)
    
    # Check satisfiability
    if opt.check() == sat:
        m = opt.model()
        start_val = m.eval(start).as_long()
        
        # Convert start time to HH:MM format
        total_minutes = start_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_str = f"{9 + hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_val = start_val + duration
        end_hours = end_val // 60
        end_minutes = end_val % 60
        end_str = f"{9 + end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()