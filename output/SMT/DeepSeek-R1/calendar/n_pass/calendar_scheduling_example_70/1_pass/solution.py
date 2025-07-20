from z3 import *

def main():
    s = Int('s')
    opt = Optimize()
    
    # Work hours: 9:00 (0 minutes) to 17:00 (480 minutes)
    opt.add(s >= 0)
    opt.add(s + 30 <= 480)
    
    # Denise's constraints
    opt.add(Or(s + 30 <= 180, s >= 210))  # Avoid 12:00-12:30
    opt.add(Or(s + 30 <= 390, s >= 420))  # Avoid 15:30-16:00
    
    # Natalie's constraints
    opt.add(s >= 150)  # Avoid 9:00-11:30
    opt.add(Or(s + 30 <= 180, s >= 240))  # Avoid 12:00-13:00
    opt.add(Or(s + 30 <= 300, s >= 330))  # Avoid 14:00-14:30
    opt.add(Or(s + 30 <= 360, s >= 480))  # Avoid 15:00-17:00 (s>=480 is impossible but included for completeness)
    
    opt.minimize(s)
    
    if opt.check() == sat:
        model = opt.model()
        start_minutes = model[s].as_long()
        
        # Calculate start time in HH:MM
        start_hour = 9 + start_minutes // 60
        start_min = start_minutes % 60
        start_time = f"{start_hour:02d}:{start_min:02d}"
        
        # Calculate end time (start_minutes + 30)
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()