from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Time representation (minutes since midnight)
    arrival = 9 * 60       # 9:00 AM (540 minutes)
    k_start = 14 * 60 + 15 # 2:15 PM (855 minutes)
    k_end = 19 * 60 + 45   # 7:45 PM (1185 minutes)
    travel = 11            # minutes

    # Meeting time variables
    start = Int('start')
    end = Int('end')

    # Basic constraints
    s.add(start >= k_start)
    s.add(end <= k_end)
    s.add(end - start >= 90)  # Minimum 90 minute meeting
    s.add(start + travel >= arrival)  # Can't meet before arriving

    # Additional constraints for robustness
    s.add(start < end)
    s.add(start >= 0, end <= 1440)  # Within one day
    s.add(end <= k_end)

    if s.check() == sat:
        m = s.model()
        try:
            # Get meeting times
            s_val = m[start].as_long()
            e_val = m[end].as_long()

            # Convert to readable time format
            def fmt_time(mins):
                h = mins // 60
                m = mins % 60
                period = 'AM' if h < 12 else 'PM'
                h = h if h <= 12 else h - 12
                return f"{h}:{m:02d} {period}"

            print(f"Optimal meeting schedule:")
            print(f"Start: {fmt_time(s_val)}")
            print(f"End:   {fmt_time(e_val)}")
            print(f"Duration: {e_val - s_val} minutes")
        except Exception as e:
            print(f"Error formatting output: {e}")
    else:
        print("No valid schedule found")

solve_scheduling()