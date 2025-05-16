from z3 import *

def main():
    opt = Optimize()
    day = Int('day')  # 0=Monday, 1=Tuesday
    start_time = Int('start_time')

    # Albert can't meet Monday (full day busy), so day must be Tuesday
    opt.add(day == 1)
    
    # Work hours: 9:00 (540) to 17:00 (1020), 30-minute meeting
    opt.add(start_time >= 540)
    opt.add(start_time + 30 <= 1020)

    # Minimize start time for earliest availability
    opt.minimize(start_time)

    # Shirley's Tuesday constraints
    # Busy 9:30-10:00 (570-600), prefers end by 10:30 (630)
    opt.add(Or(start_time + 30 <= 570, start_time >= 600))  # Avoid 570-600
    opt.add(start_time + 30 <= 630)  # End by 10:30

    # Albert's Tuesday busy intervals
    albert_busy = [
        (570, 660),   # 9:30-11:00
        (690, 750),   # 11:30-12:30
        (780, 960),   # 13:00-16:00
        (990, 1020)   # 16:30-17:00
    ]
    for s, e in albert_busy:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

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