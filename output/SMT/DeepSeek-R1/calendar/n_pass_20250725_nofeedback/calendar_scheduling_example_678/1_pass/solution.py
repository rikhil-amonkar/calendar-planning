from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # D: 0 for Monday, 1 for Tuesday
    D = Int('D')
    # S: start time in minutes from 9:00 (0 to 420)
    S = Int('S')
    
    # Constraints on D and S
    s.add(Or(D == 0, D == 1))
    s.add(S >= 0)
    s.add(S <= 420)  # because meeting must end by 17:00 (which is 480 minutes from 9:00, so 480-60=420)
    
    # Russell constraints
    # For Monday (D=0): avoid [90,120) -> condition: S+60<=90 OR S>=120
    # For Tuesday (D=1): avoid [240,270) -> condition: S+60<=240 OR S>=270, and also preference: S>=270
    russell_constraint = If(D == 0,
                            Or(S + 60 <= 90, S >= 120),
                            And(Or(S + 60 <= 240, S >= 270), S >= 270)
                           )
    s.add(russell_constraint)
    
    # Alexander constraints
    # Monday: avoid [0,150), [180,330), [360,480)
    # Tuesday: avoid [0,60), [240,300), [360,390), [420,450)
    alexander_constraint = If(D == 0,
                             And(
                                 Or(S + 60 <= 0, S >= 150),   # [0,150)
                                 Or(S + 60 <= 180, S >= 330),  # [180,330)
                                 Or(S + 60 <= 360, S >= 480)   # [360,480)
                             ),
                             And(
                                 Or(S + 60 <= 0, S >= 60),    # [0,60)
                                 Or(S + 60 <= 240, S >= 300),  # [240,300)
                                 Or(S + 60 <= 360, S >= 390),  # [360,390)
                                 Or(S + 60 <= 420, S >= 450)   # [420,450)
                             )
                            )
    s.add(alexander_constraint)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[D].as_long()
        s_val = m[S].as_long()
        
        # Convert day value to string
        day_str = "Monday" if d_val == 0 else "Tuesday"
        
        # Calculate start time in HH:MM format
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time (start time + 60 minutes)
        end_minutes = s_val + 60
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()