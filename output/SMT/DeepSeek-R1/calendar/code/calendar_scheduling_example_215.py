from z3 import *

def main():
    opt = Optimize()
    start_time = Int('start_time')  # Monday only

    # Meeting must be 30 minutes between 9:00 (540) and 17:00 (1020)
    opt.add(start_time >= 540)
    opt.add(start_time + 30 <= 1020)

    # Minimize start time to get earliest availability
    opt.minimize(start_time)

    # Cynthia's busy intervals (converted to minutes)
    cynthia_busy = [(570, 630), (690, 720), (780, 810), (900, 960)]
    for s, e in cynthia_busy:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

    # Lauren's busy intervals
    lauren_busy = [(540, 570), (630, 660), (690, 720), (780, 810), 
                   (840, 870), (900, 930), (960, 1020)]
    for s, e in lauren_busy:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

    # Robert's busy intervals
    robert_busy = [(630, 660), (690, 720), (750, 810), (840, 960)]
    for s, e in robert_busy:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

    if opt.check() == sat:
        m = opt.model()
        st = m[start_time].as_long()
        
        start_h = st // 60
        start_m = st % 60
        end_time = st + 30
        end_h = end_time // 60
        end_m = end_time % 60
        
        print(f"Monday {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()