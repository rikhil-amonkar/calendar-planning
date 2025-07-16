from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define possible days (0=Monday, 1=Tuesday, 2=Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)

    # Define start time in minutes since midnight (540=9:00, 1020=17:00)
    start = Int('start')
    s.add(start >= 540, start <= 1020 - 60)  # 1 hour meeting

    # Meeting duration is 60 minutes
    end = start + 60

    # Define blocked time ranges for each person (day, start, end)
    martha_blocks = [
        (0, 960, 1020),   # Mon 16:00-17:00
        (1, 900, 930),    # Tue 15:00-15:30
        (2, 600, 660),    # Wed 10:00-11:00
        (2, 840, 870)     # Wed 14:00-14:30
    ]

    beverly_blocks = [
        (0, 540, 810),    # Mon 9:00-13:30
        (0, 840, 1020),   # Mon 14:00-17:00
        (1, 540, 1020),   # Tue 9:00-17:00 (entire day)
        (2, 570, 930),    # Wed 9:30-15:30
        (2, 990, 1020)    # Wed 16:30-17:00
    ]

    # Function to check if a time slot is available
    def is_available(d, st, et, blocks):
        return And([Or(d != bd, et <= bs, st >= be) for (bd, bs, be) in blocks])

    # Add availability constraints
    s.add(is_available(day, start, end, martha_blocks))
    s.add(is_available(day, start, end, beverly_blocks))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        day_idx = m[day].as_long()
        start_min = m[start].as_long()
        end_min = start_min + 60
        
        # Convert to output format
        days = ['Monday', 'Tuesday', 'Wednesday']
        def time_str(minutes):
            return f"{minutes//60:02d}:{minutes%60:02d}"
        
        print("SOLUTION:")
        print(f"Day: {days[day_idx]}")
        print(f"Start Time: {time_str(start_min)}")
        print(f"End Time: {time_str(end_min)}")
    else:
        print("No solution found")

solve_scheduling()