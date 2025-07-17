from z3 import *

def main():
    day = "Monday"
    s = Int('start_time_minutes')
    solver = Solver()
    
    # Work hours: 9:00 to 17:00 (0 to 480 minutes). Meeting duration 60 minutes -> start must be between 0 and 420.
    solver.add(s >= 0)
    solver.add(s <= 420)
    
    # Ryan's constraints
    # Avoid [0, 30): meeting must start at or after 30 minutes
    solver.add(s >= 30)
    # Avoid [210, 240): meeting must end by 210 or start at or after 240
    solver.add(Or(s + 60 <= 210, s >= 240))
    
    # Denise's constraints
    # Avoid [30, 90): meeting must start at or after 90
    solver.add(s >= 90)
    # Avoid [180, 240): meeting must end by 180 or start at or after 240
    solver.add(Or(s + 60 <= 180, s >= 240))
    # Denise does not want to meet after 12:30 (210 minutes) -> meeting must end by 210
    solver.add(s + 60 <= 210)
    
    if solver.check() == sat:
        m = solver.model()
        start_minutes = m[s].as_long()
        # Calculate start time in HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        
        # Calculate end time (start_minutes + 60)
        end_minutes = start_minutes + 60
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour}:{end_minute:02d}"
        
        print(f"{day} {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()