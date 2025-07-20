from z3 import *

def main():
    # Define busy intervals in minutes from 9:00 (0 minutes)
    jacqueline = [(0, 30), (120, 150), (210, 240), (390, 420)]
    harold = [(60, 90), (240, 270), (360, 480)]
    arthur = [(0, 30), (60, 210), (330, 360), (390, 480)]
    kelly = [(0, 30), (60, 120), (150, 210), (300, 360), (390, 420)]
    
    # Create solver and variable for start time S (in minutes)
    s = Solver()
    S = Int('S')
    
    # Constraints: S in [0, 210] and multiple of 30
    s.add(S >= 0)
    s.add(S <= 210)
    s.add(S % 30 == 0)
    
    # Add constraints for each participant's busy intervals
    def add_busy_constraints(busy_intervals):
        for start, end in busy_intervals:
            s.add(Or(S + 30 <= start, S >= end))
    
    add_busy_constraints(jacqueline)
    add_busy_constraints(harold)
    add_busy_constraints(arthur)
    add_busy_constraints(kelly)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        # Convert start time to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        # Calculate end time
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes_part = end_minutes % 60
        end_time = f"{end_hours}:{end_minutes_part:02d}"
        # Print result
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()