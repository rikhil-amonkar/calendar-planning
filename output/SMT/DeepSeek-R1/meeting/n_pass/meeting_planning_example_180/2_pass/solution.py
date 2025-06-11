from z3 import *

def main():
    s = Solver()
    
    t0_leave = Int('t0_leave')
    t1_leave = Int('t1_leave')
    
    s.add(t0_leave >= 0)
    s.add(t0_leave <= 207)
    s.add(t1_leave >= 300)
    s.add(t1_leave <= 338)
    
    if s.check() == sat:
        m = s.model()
        t0 = m[t0_leave].as_long()
        t1 = m[t1_leave].as_long()
        print("Schedule in minutes after 9:00 AM:")
        print(f"  - Stay at North Beach until: {t0} minutes")
        print(f"  - Travel to Mission District (18 min), arrive at: {t0 + 18} minutes")
        print("  - Meet James from 225 to 300 minutes (75 minutes)")
        print(f"  - Leave Mission District at: {t1} minutes")
        print(f"  - Travel to The Castro (7 min), arrive at: {t1 + 7} minutes")
        print(f"  - Meet Robert from {t1 + 7} to {t1 + 37} minutes (30 minutes duration)")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()