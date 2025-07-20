from z3 import *

def main():
    # Initialize the solver
    s = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    S = Int('S')
    
    # Meeting duration is 30 minutes, and the workday is from 0 to 480 minutes (9:00 to 17:00)
    s.add(S >= 0)
    s.add(S <= 450)  # 450 + 30 = 480 (17:00)
    
    # Define busy slots for each participant (in minutes from 9:00)
    busy_slots = {
        "Judy": [(240, 270), (420, 450)],
        "Olivia": [(60, 90), (180, 240), (300, 330)],
        "Jacqueline": [(60, 90), (360, 390)],
        "Laura": [(0, 60), (90, 180), (240, 270), (330, 360), (390, 480)],
        "Tyler": [(0, 60), (120, 150), (210, 240), (300, 330), (390, 480)],
        "Lisa": [(30, 90), (120, 150), (180, 210), (240, 270), (300, 330), (420, 480)]
    }
    
    # Eric has no busy slots, so skip
    
    # Add constraints for each participant's busy slots
    for participant, slots in busy_slots.items():
        for (A, B) in slots:
            # The meeting must not overlap: it must end by A or start at/after B
            s.add(Or(S + 30 <= A, S >= B))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[S].as_long()
        
        # Convert start time to HH:MM format
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start time + 30 minutes)
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()