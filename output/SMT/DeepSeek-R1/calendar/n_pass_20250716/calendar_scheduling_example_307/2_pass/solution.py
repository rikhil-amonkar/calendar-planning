from z3 import Int, Solver, Or, sat

def main():
    # Initialize solver
    s = Solver()
    
    # Define the start time variable in minutes (from 9:00)
    start = Int('start')
    
    # Constraint: start must be between 0 and 450 (inclusive) to fit within 9:00-17:00
    s.add(start >= 0)
    s.add(start <= 450)
    
    # Busy intervals for each participant (in minutes from 9:00)
    # Format: (start_minute, end_minute) [end_minute is exclusive]
    stephen = [(60, 90), (180, 210)]
    brittany = [(120, 150), (270, 300), (390, 420), (450, 480)]
    dorothy = [(0, 30), (60, 90), (120, 210), (240, 360), (390, 480)]
    rebecca = [(30, 90), (120, 150), (180, 210), (240, 480)]
    jordan = [(0, 30), (60, 120), (150, 180), (240, 360), (390, 450)]
    
    # Ronald has no busy intervals, so no constraints needed
    
    # Add constraints for each participant's busy intervals
    for interval in stephen:
        a, b = interval
        s.add(Or(start + 30 <= a, start >= b))
    
    for interval in brittany:
        a, b = interval
        s.add(Or(start + 30 <= a, start >= b))
    
    for interval in dorothy:
        a, b = interval
        s.add(Or(start + 30 <= a, start >= b))
    
    for interval in rebecca:
        a, b = interval
        s.add(Or(start + 30 <= a, start >= b))
    
    for interval in jordan:
        a, b = interval
        s.add(Or(start + 30 <= a, start >= b))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start_minutes + 30)
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"Monday {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()