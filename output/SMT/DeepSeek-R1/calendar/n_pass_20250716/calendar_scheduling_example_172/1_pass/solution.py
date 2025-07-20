from z3 import *

def main():
    s = Int('s')
    solver = Solver()
    
    # Meeting must be within 9:00 to 17:00 (0 to 480 minutes) and end by 17:00 (s <= 450)
    solver.add(s >= 0, s <= 450)
    
    # Patrick's busy intervals (in minutes from 9:00)
    patrick = [(0, 30), (60, 90), (270, 300), (420, 450)]
    for a, b in patrick:
        solver.add(Or(s + 30 <= a, s >= b))
    
    # Kayla's busy intervals
    kayla = [(210, 270), (360, 390), (420, 450)]
    for a, b in kayla:
        solver.add(Or(s + 30 <= a, s >= b))
    
    # Carl's busy intervals
    carl = [(90, 120), (180, 210), (240, 270), (330, 480)]
    for a, b in carl:
        solver.add(Or(s + 30 <= a, s >= b))
    
    # Christian's busy intervals
    christian = [(0, 210), (240, 300), (330, 480)]
    for a, b in christian:
        solver.add(Or(s + 30 <= a, s >= b))
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        start_min = m[s].as_long()
        
        # Convert start_min to HH:MM format
        hours = start_min // 60
        minutes = start_min % 60
        start_hour = 9 + hours
        start_str = f"{start_hour}:{minutes:02d}"
        
        # Calculate end time (start_min + 30 minutes)
        end_min = start_min + 30
        hours_end = end_min // 60
        minutes_end = end_min % 60
        end_hour = 9 + hours_end
        end_str = f"{end_hour}:{minutes_end:02d}"
        
        print(f"Monday {start_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()