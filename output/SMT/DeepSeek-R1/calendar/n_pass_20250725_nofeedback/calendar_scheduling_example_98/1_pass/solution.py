from z3 import *

def main():
    s = Int('s')
    solver = Solver()
    
    # Convert times to minutes from 9:00 (0 minutes)
    # Juan: available after 10:30 (90 minutes) and must end by 15:30 (s+30 <= 390) but Ronald's constraint is tighter (s+30 <= 300)
    solver.add(s >= 90)  # Cannot start before 10:30
    solver.add(s + 30 <= 300)  # Must end by 14:00 (300 minutes) due to Ronald's schedule
    
    # Marilyn's constraints
    # Avoid 11:00-11:30 (120-150): meeting must end by 11:00 (120) or start after 11:30 (150)
    solver.add(Or(s + 30 <= 120, s >= 150))
    # Avoid 12:30-13:00 (210-240): meeting must end by 12:30 (210) or start after 13:00 (240)
    solver.add(Or(s + 30 <= 210, s >= 240))
    
    # Ronald's constraints
    # Avoid 12:00-12:30 (180-210): meeting must end by 12:00 (180) or start after 12:30 (210)
    solver.add(Or(s + 30 <= 180, s >= 210))
    # Avoid 13:00-13:30 (240-270): meeting must end by 13:00 (240) or start after 13:30 (270)
    solver.add(Or(s + 30 <= 240, s >= 270))
    
    if solver.check() == sat:
        m = solver.model()
        start_minutes = m[s].as_long()
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()