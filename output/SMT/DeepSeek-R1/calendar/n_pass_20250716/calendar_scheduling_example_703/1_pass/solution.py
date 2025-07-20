from z3 import *

def main():
    # Define variables
    day = Int('day')
    start = Int('start')
    
    # Busy intervals in minutes from 9:00
    steph_busy = {
        0: [(30, 60), (90, 120), (150, 180), (300, 330)],
        1: [(180, 240)],
        2: [(0, 60), (240, 300)]
    }
    
    betty_busy = {
        0: [(0, 60), (120, 150), (330, 360), (390, 420)],
        1: [(0, 30), (150, 180), (210, 330), (390, 420)],
        2: [(60, 150), (180, 300), (330, 480)]
    }
    
    s = Solver()
    
    # Day must be 0, 1, or 2
    s.add(day >= 0, day <= 2)
    # Start time must allow a 60-minute meeting within 9:00-17:00 (0 to 480 minutes, so start <= 420)
    s.add(start >= 0, start <= 420)
    
    # Function to generate conflict constraints for a participant
    def conflict_constraints(busy_dict, d_var):
        constraints = []
        for d_val, intervals in busy_dict.items():
            for s_busy, e_busy in intervals:
                constraints.append(If(d_var == d_val, Or(start >= e_busy, start + 60 <= s_busy), True))
        return And(constraints)
    
    # Add conflict constraints for Stephanie and Betty
    s.add(conflict_constraints(steph_busy, day))
    s.add(conflict_constraints(betty_busy, day))
    
    # Additional constraint: on Tuesday, meeting must end by 12:30 (210 minutes from 9:00)
    s.add(If(day == 1, start + 60 <= 210, True))
    
    # First, try to avoid Monday (day != 0)
    s.push()
    s.add(day != 0)
    
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_minutes = m[start].as_long()
    else:
        # If no solution avoiding Monday, try including Monday
        s.pop()
        if s.check() == sat:
            m = s.model()
            d_val = m[day].as_long()
            start_minutes = m[start].as_long()
        else:
            print("No solution found")
            return
    
    # Convert start time to HH:MM format
    total_minutes = start_minutes
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    end_minutes = start_minutes + 60
    end_hours = 9 + end_minutes // 60
    end_minutes %= 60
    
    days = ["Monday", "Tuesday", "Wednesday"]
    print(f"{days[d_val]} {hours:02d}:{minutes:02d} to {end_hours:02d}:{end_minutes:02d}")

if __name__ == "__main__":
    main()