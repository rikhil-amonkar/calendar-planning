from z3 import *

def main():
    day = Int('day')
    start = Int('start')
    s = Solver()
    
    s.add(day >= 0, day <= 4)
    s.add(start >= 0, start <= 420)
    
    busy_diane = {
        0: [(180, 210), (360, 390)],
        1: [(60, 120), (150, 180), (210, 240), (420, 480)],
        2: [(0, 30), (330, 360), (450, 480)],
        3: [(390, 450)],
        4: [(30, 150), (330, 360), (420, 480)]
    }
    
    busy_matthew = {
        0: [(0, 60), (90, 480)],
        1: [(0, 480)],
        2: [(0, 120), (180, 330), (420, 480)],
        3: [(0, 420)],
        4: [(0, 480)]
    }
    
    for d in range(5):
        for interval in busy_diane[d]:
            b_start, b_end = interval
            s.add(Implies(day == d, Or(start + 60 <= b_start, start >= b_end)))
        for interval in busy_matthew[d]:
            b_start, b_end = interval
            s.add(Implies(day == d, Or(start + 60 <= b_start, start >= b_end)))
    
    s.add(Implies(day == 2, start >= 210))
    
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_minutes = m[start].as_long()
        
        total_minutes = start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{9 + hours}:{minutes:02d}"
        
        end_minutes = start_minutes + 60
        hours_end = end_minutes // 60
        minutes_end = end_minutes % 60
        end_time = f"{9 + hours_end}:{minutes_end:02d}"
        
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_str = days[d_val]
        
        print(f"Day: {day_str}")
        print(f"Start: {start_time}")
        print(f"End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()