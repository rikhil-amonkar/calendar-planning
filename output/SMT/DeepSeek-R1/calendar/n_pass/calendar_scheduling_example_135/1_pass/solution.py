from z3 import *

def main():
    # Define the variable for the slot index (0 to 15)
    T = Int('T')
    solver = Solver()
    
    # T must be between 0 and 15 inclusive (16 slots)
    solver.add(T >= 0, T <= 15)
    
    # Ashley's busy intervals in minutes from 9:00 (start, end)
    ashley_busy = [(60, 90), (120, 180), (210, 240), (360, 420)]
    for (s, e) in ashley_busy:
        # The meeting slot is [T*30, T*30+30)
        # It should not overlap with [s, e): either meeting ends before s or starts after e
        solver.add(Or(T*30 >= e, T*30 + 30 <= s))
    
    # Ronald's busy intervals
    ronald_busy = [(0, 30), (60, 150), (210, 300), (330, 480)]
    for (s, e) in ronald_busy:
        solver.add(Or(T*30 >= e, T*30 + 30 <= s))
    
    # Larry's busy intervals
    larry_busy = [(0, 180), (240, 480)]
    for (s, e) in larry_busy:
        solver.add(Or(T*30 >= e, T*30 + 30 <= s))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        t_val = model[T].as_long()
        
        # Calculate start time in minutes from 9:00
        start_minutes = t_val * 30
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the time as HH:MM
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        # According to the problem, there is a solution, but handle no solution case
        print("SOLUTION: No solution found")

if __name__ == "__main__":
    main()