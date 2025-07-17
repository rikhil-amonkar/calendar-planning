from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time in minutes from 9:00 (0 minutes = 9:00)
    start = Int('start')
    
    # Possible start times: every 30 minutes from 0 (9:00) to 450 (16:30)
    possible_starts = [0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330, 360, 390, 420, 450]
    s.add(Or([start == ps for ps in possible_starts]))
    
    # Define busy intervals for each participant (in minutes from 9:00)
    katherine_busy = [(180, 210), (240, 330)]
    rebecca_busy = []
    julie_busy = [(0, 30), (90, 120), (270, 300), (360, 390)]
    angela_busy = [(0, 60), (90, 120), (150, 300), (330, 360), (450, 480)]
    nicholas_busy = [(30, 120), (150, 270), (300, 420), (450, 480)]
    carl_busy = [(0, 120), (150, 210), (240, 330), (360, 420), (450, 480)]
    
    # Function to add busy constraints for a participant
    def add_busy_constraints(busy_intervals):
        for (b_start, b_end) in busy_intervals:
            s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # Add constraints for each participant
    add_busy_constraints(katherine_busy)
    add_busy_constraints(rebecca_busy)
    add_busy_constraints(julie_busy)
    add_busy_constraints(angela_busy)
    add_busy_constraints(nicholas_busy)
    add_busy_constraints(carl_busy)
    
    # First, try to find a slot at or after 15:00 (360 minutes)
    s.push()
    s.add(start >= 360)
    
    if s.check() == sat:
        model = s.model()
    else:
        s.pop()
        if s.check() == sat:
            model = s.model()
        else:
            print("SOLUTION not found")
            return
    
    start_val = model[start].as_long()
    
    # Convert minutes back to time string
    total_minutes = start_val
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    
    end_minutes = total_minutes + 30
    end_hours = 9 + end_minutes // 60
    end_minutes = end_minutes % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    
    # Output the solution
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()