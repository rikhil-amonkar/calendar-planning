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
            # Safely extract values
            def get_value(var):
                val = m[var]
                if is_int_value(val):
                    return val.as_long()
                return None

            s_val = get_value(start)
            e_val = get_value(end)

            if s_val is None or e_val is None:
                raise ValueError("Invalid model values")

            # Convert to readable time format
            def fmt_time(mins):
                h = mins // 60
                m = mins % 60
                period = 'AM' if h < 12 else 'PM'
                h = h if h <= 12 else h - 12
                if h == 0: h = 12  # Handle midnight
                return f"{h}:{m:02d} {period}"

            print(f"Optimal meeting schedule:")
            print(f"Start: {fmt_time(s_val)}")
            print(f"End:   {fmt_time(e_val)}")
            print(f"Duration: {e_val - s_val} minutes")
            
            return True
        except Exception as e:
            print(f"Error processing solution: {e}")
            return False
    else:
        print("No valid schedule found")
        return False

# Run the solver
if __name__ == "__main__":
    solve_scheduling()