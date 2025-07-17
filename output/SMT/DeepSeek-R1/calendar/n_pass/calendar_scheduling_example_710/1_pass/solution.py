from z3 import Solver, Int, Or, And, If, sat

def main():
    s = Solver()
    
    # Day: 0 = Monday, 1 = Tuesday
    day = Int('day')
    start = Int('start')  # in minutes from 9:00
    
    # Day must be Monday (0) or Tuesday (1)
    s.add(Or(day == 0, day == 1))
    # Start time must be between 0 and 450 (since 480 - 30 = 450)
    s.add(start >= 0, start <= 450)
    
    # Busy times in minutes from 9:00
    # Cheryl on Monday: [0, 30), [150, 240), [390, 420)
    cheryl_mon_constraints = And(
        Or(start + 30 <= 0, start >= 30),
        Or(start + 30 <= 150, start >= 240),
        Or(start + 30 <= 390, start >= 420)
    )
    # Kyle on Monday: [0, 480)
    kyle_mon_constraints = Or(start + 30 <= 0, start >= 480)
    
    # Cheryl on Tuesday: [360, 390)
    cheryl_tue_constraints = Or(start + 30 <= 360, start >= 390)
    # Kyle on Tuesday: [30, 480)
    kyle_tue_constraints = Or(start + 30 <= 30, start >= 480)
    
    # Add constraints based on the day
    s.add(If(day == 0, 
             And(cheryl_mon_constraints, kyle_mon_constraints),
             If(day == 1,
                And(cheryl_tue_constraints, kyle_tue_constraints),
                False)))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        st = m[start].as_long()
        
        # Convert start time to HH:MM
        hours = 9 + st // 60
        minutes = st % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = st + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        day_str = "Monday" if d == 0 else "Tuesday"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()