from z3 import *

def main():
    # Define the busy intervals for Bryan and Nicholas
    bryan_busy = [
        (3, 30, 60),    # Thursday 9:30-10:00
        (3, 150, 180),  # Thursday 12:30-13:00
        (4, 90, 120),   # Friday 10:30-11:00
        (4, 300, 330)   # Friday 14:00-14:30
    ]
    
    nicholas_busy = [
        (0, 150, 180),  # Monday 11:30-12:00
        (0, 240, 390),  # Monday 13:00-15:30
        (1, 0, 30),     # Tuesday 9:00-9:30
        (1, 120, 270),  # Tuesday 11:00-13:30
        (1, 300, 450),  # Tuesday 14:00-16:30
        (2, 0, 30),     # Wednesday 9:00-9:30
        (2, 60, 120),   # Wednesday 10:00-11:00
        (2, 150, 270),  # Wednesday 11:30-13:30
        (2, 300, 330),  # Wednesday 14:00-14:30
        (2, 360, 450),  # Wednesday 15:00-16:30
        (3, 90, 150),   # Thursday 10:30-11:30
        (3, 180, 210),  # Thursday 12:00-12:30
        (3, 360, 390),  # Thursday 15:00-15:30
        (3, 450, 480),  # Thursday 16:30-17:00
        (4, 0, 90),     # Friday 9:00-10:30
        (4, 120, 180),  # Friday 11:00-12:00
        (4, 210, 330),  # Friday 12:30-14:30
        (4, 390, 420),  # Friday 15:30-16:00
        (4, 450, 480)   # Friday 16:30-17:00
    ]
    
    # Create Z3 variables
    day = Int('day')
    start_time = Int('start_time')
    
    # Create solver
    s = Solver()
    
    # Basic constraints: day between 0 and 4, start_time between 0 and 420
    s.add(day >= 0, day <= 4)
    s.add(start_time >= 0, start_time <= 420)
    
    # Function to add non-overlap constraints for a list of busy intervals
    def add_busy_constraints(busy_list):
        for d, s_busy, e_busy in busy_list:
            s.add(Implies(day == d, Or(start_time + 60 <= s_busy, start_time >= e_busy)))
    
    # Add constraints for Bryan and Nicholas
    add_busy_constraints(bryan_busy)
    add_busy_constraints(nicholas_busy)
    
    # First, try with preference constraints: avoid Tuesday (1), Monday (0), and Thursday (3)
    s.push()
    s.add(And(day != 0, day != 1, day != 3))
    
    # Check for solution with preferences
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
    else:
        # Remove preference constraints and try again
        s.pop()
        if s.check() == sat:
            m = s.model()
            day_val = m[day].as_long()
            start_val = m[start_time].as_long()
        else:
            # According to the problem, a solution exists
            print("Unexpected: No solution found")
            return
    
    # Map day value to string
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_str = days[day_val]
    
    # Calculate start time in HH:MM format
    total_minutes_start = start_val
    hour_start = 9 + total_minutes_start // 60
    minute_start = total_minutes_start % 60
    start_str = f"{hour_start}:{minute_start:02d}"
    
    # Calculate end time in HH:MM format
    total_minutes_end = start_val + 60
    hour_end = 9 + total_minutes_end // 60
    minute_end = total_minutes_end % 60
    end_str = f"{hour_end}:{minute_end:02d}"
    
    # Output the solution
    print(f"Day: {day_str}")
    print(f"Start time: {start_str}")
    print(f"End time: {end_str}")

if __name__ == "__main__":
    main()