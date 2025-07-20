from z3 import *

def main():
    start = Int('start')
    constraints = []
    
    # Work hours constraint: meeting must be between 9:00 (540) and 17:00 (1020)
    constraints.append(start >= 540)
    constraints.append(start <= 990)  # 990 + 30 = 1020 (17:00)
    
    # Busy intervals for each participant (converted to minutes)
    busy_intervals = [
        # Kathleen
        (14*60+30, 15*60+30),  # 14:30 to 15:30 -> (870, 930)
        # Carolyn
        (12*60, 12*60+30),      # 12:00 to 12:30 -> (720, 750)
        (13*60, 13*60+30),      # 13:00 to 13:30 -> (780, 810)
        # Cheryl
        (9*60, 9*60+30),        # 9:00 to 9:30 -> (540, 570)
        (10*60, 11*60+30),      # 10:00 to 11:30 -> (600, 690)
        (12*60+30, 13*60+30),   # 12:30 to 13:30 -> (750, 810)
        (14*60, 17*60),         # 14:00 to 17:00 -> (840, 1020)
        # Virginia
        (9*60+30, 11*60+30),    # 9:30 to 11:30 -> (570, 690)
        (12*60, 12*60+30),      # 12:00 to 12:30 -> (720, 750)
        (13*60, 13*60+30),      # 13:00 to 13:30 -> (780, 810)
        (14*60+30, 15*60+30),   # 14:30 to 15:30 -> (870, 930)
        (16*60, 17*60),         # 16:00 to 17:00 -> (960, 1020)
        # Angela
        (9*60+30, 10*60),       # 9:30 to 10:00 -> (570, 600)
        (10*60+30, 11*60+30),   # 10:30 to 11:30 -> (630, 690)
        (12*60, 12*60+30),      # 12:00 to 12:30 -> (720, 750)
        (13*60, 13*60+30),      # 13:00 to 13:30 -> (780, 810)
        (14*60, 16*60+30)       # 14:00 to 16:30 -> (840, 990)
    ]
    
    # Add constraints for each busy interval: meeting must not overlap
    for (s_busy, e_busy) in busy_intervals:
        constraints.append(Or(start + 30 <= s_busy, start >= e_busy))
    
    # Create solvers
    s1 = Solver()  # with Roger's preference (start >= 12:30 = 750 minutes)
    s2 = Solver()  # without preference
    
    for c in constraints:
        s1.add(c)
        s2.add(c)
    s1.add(start >= 750)  # Roger's preference
    
    start_val = None
    if s1.check() == sat:
        model = s1.model()
        start_val = model[start].as_long()
    else:
        if s2.check() == sat:
            model = s2.model()
            start_val = model[start].as_long()
        else:
            # Fallback: though problem states a solution exists
            start_val = 540
    
    # Convert minutes back to HH:MM
    hours = start_val // 60
    minutes = start_val % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    end_val = start_val + 30
    end_hours = end_val // 60
    end_minutes = end_val % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()