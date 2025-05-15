from z3 import *

def main():
    opt = Optimize()
    day = Int('day')
    start_time = Int('start_time')

    # Day constraints (0=Monday to 4=Friday)
    opt.add(day >= 0, day <= 4)
    
    # Meeting must start between 9:00 (540) and end by 17:00 (1020)
    opt.add(start_time >= 540)
    opt.add(start_time + 60 <= 1020)

    # Define total minutes since Monday 00:00 for optimization
    total_time = day * 1440 + start_time
    opt.minimize(total_time)

    # Nicole's schedule constraints
    nicole_intervals = [
        (1, 960, 990),   # Tuesday 16:00-16:30
        (2, 900, 930),   # Wednesday 15:00-15:30
        (4, 720, 750),   # Friday 12:00-12:30
        (4, 930, 960),   # Friday 15:30-16:00
    ]
    for d, s, e in nicole_intervals:
        opt.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

    # Daniel's schedule constraints
    daniel_intervals = [
        (0, 540, 750), (0, 780, 810), (0, 840, 990),         # Monday
        (1, 540, 630), (1, 690, 750), (1, 780, 810),         # Tuesday
        (1, 900, 960), (1, 990, 1020),                       # Tuesday
        (2, 540, 600), (2, 660, 750), (2, 780, 810),         # Wednesday
        (2, 840, 870), (2, 990, 1020),                       # Wednesday
        (3, 660, 720), (3, 780, 840), (3, 900, 930),         # Thursday
        (4, 600, 660), (4, 690, 720), (4, 750, 870),         # Friday
        (4, 900, 930), (4, 960, 990),                        # Friday
    ]
    for d, s, e in daniel_intervals:
        opt.add(Implies(day == d, Or(start_time + 60 <= s, start_time >= e)))

    if opt.check() == sat:
        m = opt.model()
        d = m[day].as_long()
        st = m[start_time].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        start_h = st // 60
        start_m = st % 60
        end_time = st + 60
        end_h = end_time // 60
        end_m = end_time % 60
        
        print(f"{days[d]} {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()