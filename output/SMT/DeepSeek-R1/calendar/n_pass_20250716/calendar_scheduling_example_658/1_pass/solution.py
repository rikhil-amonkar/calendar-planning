from z3 import *

def main():
    # Initialize variables
    day = Int('day')
    start = Int('start')
    
    # Create solver for Step 1 (with preference)
    s1 = Solver()
    
    # Hard constraints
    s1.add(Or(day == 0, day == 1))  # Day is Monday (0) or Tuesday (1)
    s1.add(start >= 540)             # Meeting starts at or after 9:00
    s1.add(start <= 990)             # Meeting starts at or before 16:30 (to end by 17:00)
    
    # Define busy intervals (half-open [start, end))
    shirley_monday = [(630, 660), (720, 750), (960, 990)]
    shirley_tuesday = [(570, 600)]
    albert_monday = [(540, 1020)]
    albert_tuesday = [(570, 660), (690, 750), (780, 960), (990, 1020)]
    
    # Function to add non-overlap constraints
    def no_overlap(day_val, intervals):
        constraints = []
        for (busy_start, busy_end) in intervals:
            constraints.append(Or(start + 30 <= busy_start, start >= busy_end))
        return Implies(day == day_val, And(*constraints))
    
    # Add non-overlap constraints for Shirley
    s1.add(no_overlap(0, shirley_monday))
    s1.add(no_overlap(1, shirley_tuesday))
    # Add non-overlap constraints for Albert
    s1.add(no_overlap(0, albert_monday))
    s1.add(no_overlap(1, albert_tuesday))
    
    # Preference constraint: on Tuesday, meeting must end by 10:30 (630 minutes)
    s1.add(Implies(day == 1, start + 30 <= 630))
    
    # Step 1: Try to solve with preference
    if s1.check() == sat:
        m = s1.model()
    else:
        # Step 2: Solve without preference
        s2 = Solver()
        s2.add(Or(day == 0, day == 1))
        s2.add(start >= 540, start <= 990)
        s2.add(no_overlap(0, shirley_monday))
        s2.add(no_overlap(1, shirley_tuesday))
        s2.add(no_overlap(0, albert_monday))
        s2.add(no_overlap(1, albert_tuesday))
        s2.check()
        m = s2.model()
    
    # Extract solution
    day_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = start_val + 30
    
    # Convert day to string
    day_str = "Monday" if day_val == 0 else "Tuesday"
    
    # Convert start and end times to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = format_time(start_val)
    end_str = format_time(end_val)
    
    # Output the solution
    print(f"Day: {day_str}")
    print(f"Start time: {start_str}")
    print(f"End time: {end_str}")

if __name__ == "__main__":
    main()