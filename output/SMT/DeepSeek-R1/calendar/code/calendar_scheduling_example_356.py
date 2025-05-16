from z3 import *

def main():
    opt = Optimize()
    start_time = Int('start_time')  # Monday only

    # Meeting must be 30 minutes between 9:00 (540) and 17:00 (1020)
    opt.add(start_time >= 540)
    opt.add(start_time + 30 <= 1020)

    # Add Angela's preference as soft constraint (prefer start_time >= 900)
    opt.add_soft(start_time >= 900)

    # Minimize start time to get earliest possible slot
    opt.minimize(start_time)

    # Katherine's busy intervals (minutes)
    katherine = [(720, 750), (780, 870)]
    for s, e in katherine:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

    # Julie's busy intervals
    julie = [(540, 570), (630, 660), (810, 840), (900, 930)]
    for s, e in julie:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

    # Angela's busy intervals
    angela = [(540, 600), (630, 660), (690, 840), (870, 900), (990, 1020)]
    for s, e in angela:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

    # Nicholas's busy intervals
    nicholas = [(570, 660), (690, 810), (840, 960), (990, 1020)]
    for s, e in nicholas:
        opt.add(Or(start_time + 30 <= s, start_time >= e))

    # Carl's busy intervals
    carl = [(540, 660), (690, 750), (780, 870), (900, 960), (990, 1020)]
    for s, e in carl:
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