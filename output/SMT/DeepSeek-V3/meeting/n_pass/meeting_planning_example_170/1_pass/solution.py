from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Arrival time at North Beach: 9:00 AM (540 minutes)
    emily_start_available = 16 * 60  # 4:00 PM (960 minutes since midnight, 420 since 9:00 AM)
    emily_end_available = 17 * 60 + 15  # 5:15 PM (1035 minutes since midnight, 495 since 9:00 AM)
    margaret_start_available = 19 * 60  # 7:00 PM (1140 minutes since midnight, 600 since 9:00 AM)
    margaret_end_available = 21 * 60  # 9:00 PM (1260 minutes since midnight, 720 since 9:00 AM)

    # Variables for meeting start and end times (in minutes since 9:00 AM)
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Travel times (in minutes)
    north_beach_to_union_square = 7
    north_beach_to_russian_hill = 4
    union_square_to_north_beach = 10
    union_square_to_russian_hill = 13
    russian_hill_to_north_beach = 5
    russian_hill_to_union_square = 11

    # Constraints for Emily
    s.add(emily_start >= emily_start_available - 540)  # Convert to minutes since 9:00 AM
    s.add(emily_end <= emily_end_available - 540)
    s.add(emily_end - emily_start >= 45)

    # Constraints for Margaret
    s.add(margaret_start >= margaret_start_available - 540)
    s.add(margaret_end <= margaret_end_available - 540)
    s.add(margaret_end - margaret_start >= 120)

    # Travel constraints
    # Assume we start at North Beach at time 0 (9:00 AM)
    # We can either go to Union Square or Russian Hill first, but we must meet Emily and Margaret in their time windows.
    # Since Emily is only available in the afternoon, and Margaret in the evening, we can meet Emily first, then Margaret.

    # Option 1: Go to Union Square first (to meet Emily), then to Russian Hill (to meet Margaret)
    # Time to reach Union Square: 7 minutes
    s.add(emily_start >= 7)  # Travel from North Beach to Union Square takes 7 minutes
    # Time to go from Union Square to Russian Hill: 13 minutes
    s.add(margaret_start >= emily_end + 13)

    # Option 2: Go to Russian Hill first, then to Union Square. But Margaret is only available in the evening, so this is not feasible.
    # Therefore, Option 1 is the only feasible path.

    # Maximize the total time spent with friends
    total_time = (emily_end - emily_start) + (margaret_end - margaret_start)
    s.maximize(total_time)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        print("Meeting with Emily:")
        print(f"Start: {540 + m[emily_start].as_long()} minutes since midnight ({(540 + m[emily_start].as_long()) // 60}:{(540 + m[emily_start].as_long()) % 60:02d})")
        print(f"End: {540 + m[emily_end].as_long()} minutes since midnight ({(540 + m[emily_end].as_long()) // 60}:{(540 + m[emily_end].as_long()) % 60:02d})")
        print("Meeting with Margaret:")
        print(f"Start: {540 + m[margaret_start].as_long()} minutes since midnight ({(540 + m[margaret_start].as_long()) // 60}:{(540 + m[margaret_start].as_long()) % 60:02d})")
        print(f"End: {540 + m[margaret_end].as_long()} minutes since midnight ({(540 + m[margaret_end].as_long()) // 60}:{(540 + m[margaret_end].as_long()) % 60:02d})")
        print(f"Total time with friends: {m[emily_end].as_long() - m[emily_start].as_long() + m[margaret_end].as_long() - m[margaret_start].as_long()} minutes")
    else:
        print("No feasible schedule found.")

solve_scheduling()