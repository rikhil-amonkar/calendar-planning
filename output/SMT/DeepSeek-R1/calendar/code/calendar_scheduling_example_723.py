from z3 import *

def main():
    opt = Optimize()
    day = Int('day')  # 0=Monday, 2=Wednesday (Arthur can't meet Tuesday)
    start_time = Int('start_time')

    # Day constraints (0=Monday, 2=Wednesday)
    opt.add(Or(day == 0, day == 2))
    
    # Work hours: 9:00 (540) to 17:00 (1020), 30-minute meeting
    opt.add(start_time >= 540)
    opt.add(start_time + 30 <= 1020)

    # Minimize total minutes since Monday 00:00 for earliest time
    total_time = day * 1440 + start_time
    opt.minimize(total_time)

    # Arthur's schedule (Monday and Wednesday)
    arthur_intervals = [
        (0, 660, 690), (0, 810, 840), (0, 900, 930),   # Monday
        (2, 600, 630), (2, 660, 690), (2, 720, 750),   # Wednesday
        (2, 840, 870), (2, 960, 990)                   # Wednesday
    ]

    # Michael's schedule (Monday and Wednesday)
    michael_intervals = [
        (0, 540, 720), (0, 750, 780), (0, 840, 870), (0, 900, 1020),  # Monday
        (2, 600, 750), (2, 780, 810)                                  # Wednesday
    ]

    # Add constraints for both participants
    for d, s, e in arthur_intervals + michael_intervals:
        opt.add(Implies(day == d, Or(start_time + 30 <= s, start_time >= e)))

    if opt.check() == sat:
        m = opt.model()
        d = m[day].as_long()
        st = m[start_time].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        start_h = st // 60
        start_m = st % 60
        end_time = st + 30
        end_h = end_time // 60
        end_m = end_time % 60
        
        print(f"{days[d]} {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()