from z3 import Int, Solver, Or, And

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the start time variable in minutes from 9:00
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 30
    
    # Harold's constraint: meeting must end by 13:00 (240 minutes from 9:00)
    s.add(start >= 0, start <= 210)  # 210 minutes = 12:30, so meeting ends at 13:00
    
    # Busy intervals for each participant (in minutes from 9:00, half-open [start, end))
    jacqueline = [(0, 30), (120, 150), (210, 240)]
    harold = [(60, 90)]
    arthur = [(0, 30), (60, 210)]
    kelly = [(0, 30), (60, 120), (150, 210)]
    
    # Add constraints for each participant's busy intervals
    for a, b in jacqueline:
        s.add(Or(start + duration <= a, start >= b))
    for a, b in harold:
        s.add(Or(start + duration <= a, start >= b))
    for a, b in arthur:
        s.add(Or(start + duration <= a, start >= b))
    for a, b in kelly:
        s.add(Or(start + duration <= a, start >= b))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert start minutes to time string
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the time string without leading zeros for hours, but with two-digit minutes
        start_str = f"{start_hour}:{start_minute:02d}"
        end_str = f"{end_hour}:{end_minute:02d}"
        
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()