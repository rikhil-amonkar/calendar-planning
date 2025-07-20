from z3 import *

def main():
    s = Solver()
    
    t0_leave = Int('t0_leave')
    t1_leave = Int('t1_leave')
    
    s.add(t0_leave >= 0)
    s.add(t1_leave >= t0_leave + 18)
    s.add(t0_leave + 18 <= 225)
    s.add(t1_leave >= 300)
    s.add(t1_leave + 37 <= 375)
    
    if s.check() == sat:
        m = s.model()
        leave0 = m[t0_leave].as_long()
        leave1 = m[t1_leave].as_long()
        print("Schedule in minutes after 9:00 AM:")
        print(f"  - Stay at North Beach until: {leave0} minutes")
        print(f"  - Travel to Mission District (18 min), arrive at: {leave0 + 18} minutes")
        print(f"  - Meet James from 225 to 300 minutes (exactly 75 minutes)")
        print(f"  - Leave Mission District at: {leave1} minutes")
        print(f"  - Travel to The Castro (7 min), arrive at: {leave1 + 7} minutes")
        print(f"  - Meet Robert from {leave1 + 7} to {leave1 + 37} minutes (30 minutes duration)")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()