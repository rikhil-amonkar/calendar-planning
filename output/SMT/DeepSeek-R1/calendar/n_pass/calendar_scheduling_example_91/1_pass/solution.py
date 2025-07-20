from z3 import *

def main():
    s = Int('s')
    
    # Convert busy times to minutes from 9:00
    # Danielle's meetings
    danielle = [(0, 60), (90, 120), (330, 360), (390, 420), (450, 480)]
    # Bruce's meetings
    bruce = [(120, 150), (210, 240), (300, 330), (390, 420)]
    # Eric's meetings
    eric = [(0, 30), (60, 120), (150, 240), (330, 390)]
    
    all_busy = [danielle, bruce, eric]
    
    constraints = [s >= 0, s <= 420]  # Meeting must start by 16:00 to end by 17:00
    
    for person in all_busy:
        for interval in person:
            a, b = interval
            constraints.append(Or(s + 60 <= a, s >= b))
    
    solver = Solver()
    solver.add(constraints)
    
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.eval(s).as_long()
        
        # Calculate start time (HH:MM)
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time (start_minutes + 60 minutes)
        end_minutes = start_minutes + 60
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()