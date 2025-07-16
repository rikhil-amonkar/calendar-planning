from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM (540 minutes since midnight)
    emily_start_available = 16 * 60  # 4:00 PM (960 minutes since midnight)
    emily_end_available = 17 * 60 + 15  # 5:15 PM (1035 minutes since midnight)
    margaret_start_available = 19 * 60  # 7:00 PM (1140 minutes since midnight)
    margaret_end_available = 21 * 60  # 9:00 PM (1260 minutes since midnight)

    # Variables for meeting start and end times (in minutes since midnight)
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
    s.add(emily_start >= emily_start_available)
    s.add(emily_end <= emily_end_available)
    s.add(emily_end - emily_start >= 45)

    # Constraints for Margaret
    s.add(margaret_start >= margaret_start_available)
    s.add(margaret_end <= margaret_end_available)
    s.add(margaret_end - margaret_start >= 120)

    # Travel constraints
    # Start at North Beach at 9:00 AM (540 minutes)
    # Option 1: Go to Union Square first (to meet Emily), then to Russian Hill (to meet Margaret)
    # Time to reach Union Square: 7 minutes
    s.add(emily_start >= arrival_time + north_beach_to_union_square)
    # Time to go from Union Square to Russian Hill: 13 minutes
    s.add(margaret_start >= emily_end + union_square_to_russian_hill)

    # Maximize the total time spent with friends
    total_time = (emily_end - emily_start) + (margaret_end - margaret_start)
    s.maximize(total_time)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        print("Meeting with Emily:")
        print(f"Start: {m[emily_start].as_long() // 60}:{m[emily_start].as_long() % 60:02d}")
        print(f"End: {m[emily_end].as_long() // 60}:{m[emily_end].as_long() % 60:02d}")
        print("Meeting with Margaret:")
        print(f"Start: {m[margaret_start].as_long() // 60}:{m[margaret_start].as_long() % 60:02d}")
        print(f"End: {m[margaret_end].as_long() // 60}:{m[margaret_end].as_long() % 60:02d}")
        print(f"Total time with friends: {m[emily_end].as_long() - m[emily_start].as_long() + m[margaret_end].as_long() - m[margaret_start].as_long()} minutes")
    else:
        print("No feasible schedule found.")

solve_scheduling()