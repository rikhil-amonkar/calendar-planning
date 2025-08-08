from z3 import *

def main():
    D = Int('D')
    S = Int('S')
    
    s = Solver()
    
    case0 = And(D == 0, False)  # Monday not possible
    case1 = And(D == 1, False)  # Tuesday not possible
    
    # Wednesday constraints
    wed_nicole = And(
        Or(S + 30 <= 60, S >= 120),   # Avoid 10:00-11:00
        Or(S + 30 <= 210, S >= 360),  # Avoid 12:30-15:00
        Or(S + 30 <= 420, S >= 480)   # Avoid 16:00-17:00
    )
    wed_ruth = And(
        Or(S + 30 <= 0, S >= 90),     # Avoid 9:00-10:30
        Or(S + 30 <= 120, S >= 150),  # Avoid 11:00-11:30
        Or(S + 30 <= 180, S >= 210)   # Avoid 12:00-12:30 and 13:30-15:30 (handled by preference)
    )
    wed_preference = S <= 240  # End by 13:30 (270 minutes from 9:00)
    case2 = And(D == 2, wed_nicole, wed_ruth, wed_preference, S >= 0, S <= 450)
    
    s.add(Or(case0, case1, case2))
    s.add(D >= 0, D <= 2)
    s.add(S >= 0, S <= 450)
    
    if s.check() == sat:
        m = s.model()
        d_val = m[D].as_long()
        s_val = m[S].as_long()
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        total_minutes = s_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_minute = minutes
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_minutes = total_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        print("Day:", day_str)
        print("Start Time:", start_time)
        print("End Time:", end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()