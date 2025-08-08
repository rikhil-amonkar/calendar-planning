from z3 import *

def main():
    day = Int('day')
    start_minutes = Int('start_minutes')
    
    base_constraints = [
        day >= 0,
        day <= 4,
        start_minutes >= 0,
        start_minutes <= 450  # 450 + 30 = 480 (17:00)
    ]
    
    eugene_busy = {
        0: [(120, 180), (270, 300), (330, 360), (420, 450)],  # Monday
        2: [(0, 30), (120, 150), (180, 210), (270, 360)],    # Wednesday
        3: [(30, 60), (120, 210)],                           # Thursday
        4: [(90, 120), (180, 210), (240, 270)]               # Friday
    }
    
    eric_busy = {
        0: [(0, 480)],   # Monday
        1: [(0, 480)],   # Tuesday
        2: [(0, 150), (180, 300), (330, 450)],  # Wednesday
        3: [(0, 480)],   # Thursday
        4: [(0, 120), (150, 480)]   # Friday
    }
    
    def free_slot(start, intervals):
        cond = True
        for (s_busy, e_busy) in intervals:
            cond = And(cond, Or(start + 30 <= s_busy, start >= e_busy))
        return cond
    
    eugene_cond = True
    for d, intervals in eugene_busy.items():
        eugene_cond = And(eugene_cond, If(day == d, free_slot(start_minutes, intervals), True))
    
    eric_cond = True
    for d, intervals in eric_busy.items():
        eric_cond = And(eric_cond, If(day == d, free_slot(start_minutes, intervals), True))
    
    s1 = Solver()
    s1.add(base_constraints)
    s1.add(eugene_cond)
    s1.add(eric_cond)
    s1.add(day != 2)  # Avoid Wednesday if possible
    
    if s1.check() == sat:
        m = s1.model()
    else:
        s2 = Solver()
        s2.add(base_constraints)
        s2.add(eugene_cond)
        s2.add(eric_cond)
        if s2.check() == sat:
            m = s2.model()
        else:
            print("No solution found")
            return
    
    day_val = m.eval(day).as_long()
    start_minutes_val = m.eval(start_minutes).as_long()
    
    total_minutes = start_minutes_val
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_hour = 9 + hours
    start_min = minutes
    start_time = f"{start_hour:02d}:{start_min:02d}"
    
    end_minutes_val = start_minutes_val + 30
    end_hours = 9 + (end_minutes_val // 60)
    end_minutes = end_minutes_val % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    
    days_map = {
        0: "Monday",
        1: "Tuesday",
        2: "Wednesday",
        3: "Thursday",
        4: "Friday"
    }
    day_str = days_map[day_val]
    
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()