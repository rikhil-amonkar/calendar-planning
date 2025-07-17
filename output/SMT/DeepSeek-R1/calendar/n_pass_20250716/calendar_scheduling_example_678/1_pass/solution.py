from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Variables
    day = Int('day')
    start = Int('start')
    
    # Day must be 0 (Monday) or 1 (Tuesday)
    s.add(Or(day == 0, day == 1))
    
    # Start time must be between 0 and 420 minutes (9:00 to 16:00 inclusive for a 1-hour meeting)
    s.add(start >= 0)
    s.add(start <= 420)
    
    # Russell's constraints
    # Monday: avoid [90, 120) -> 10:30 to 11:00
    russell_monday = Or(start + 60 <= 90, start >= 120)
    
    # Tuesday: avoid [240, 270) -> 13:00 to 13:30 and start at or after 270 (13:30)
    russell_tuesday_busy = Or(start + 60 <= 240, start >= 270)
    russell_tuesday_pref = (start >= 270)
    russell_tuesday = And(russell_tuesday_busy, russell_tuesday_pref)
    
    # Combine Russell's constraints based on day
    s.add(If(day == 0, russell_monday, russell_tuesday))
    
    # Alexander's constraints
    # Monday: avoid [0,150), [180,330), [360,480)
    alex_monday = And(
        Or(start + 60 <= 0, start >= 150),   # Avoid [0,150)
        Or(start + 60 <= 180, start >= 330),  # Avoid [180,330)
        Or(start + 60 <= 360, start >= 480)   # Avoid [360,480)
    )
    
    # Tuesday: avoid [0,60), [240,300), [360,390), [420,450)
    alex_tuesday = And(
        Or(start + 60 <= 0, start >= 60),    # Avoid [0,60)
        Or(start + 60 <= 240, start >= 300),  # Avoid [240,300)
        Or(start + 60 <= 360, start >= 390),  # Avoid [360,390)
        Or(start + 60 <= 420, start >= 450)   # Avoid [420,450)
    )
    
    # Combine Alexander's constraints based on day
    s.add(If(day == 0, alex_monday, alex_tuesday))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        st = m[start].as_long()
        
        # Convert start time to hours and minutes
        hours = st // 60
        minutes = st % 60
        start_time = f"{9 + hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_time_minutes = st + 60
        end_hours = end_time_minutes // 60
        end_minutes = end_time_minutes % 60
        end_time = f"{9 + end_hours:02d}:{end_minutes:02d}"
        
        # Map day to string
        day_str = "Monday" if d == 0 else "Tuesday"
        
        print(f"Meeting scheduled on {day_str} from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()