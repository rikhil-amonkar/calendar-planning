from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting times (in minutes since midnight)
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Time constants (in minutes since midnight)
    arrival_time = 540  # 9:00 AM
    richard_available_start = 525  # 8:45 AM
    richard_available_end = 780    # 1:00 PM
    charles_available_start = 585  # 9:45 AM
    charles_available_end = 780    # 1:00 PM

    # Travel times (in minutes)
    bayview_to_union_square = 17
    bayview_to_presidio = 31
    union_square_to_presidio = 24
    presidio_to_union_square = 22

    # Base constraints for both scenarios
    s.add(richard_end - richard_start >= 120)  # At least 2 hours with Richard
    s.add(charles_end - charles_start >= 120)  # At least 2 hours with Charles
    s.add(richard_start >= richard_available_start)
    s.add(richard_end <= richard_available_end)
    s.add(charles_start >= charles_available_start)
    s.add(charles_end <= charles_available_end)

    # Create two scenarios
    scenario1 = Solver()
    scenario2 = Solver()

    # Scenario 1: Meet Richard first, then Charles
    scenario1.add(richard_start >= arrival_time + bayview_to_union_square)
    scenario1.add(charles_start >= richard_end + union_square_to_presidio)
    for c in s.assertions():
        scenario1.add(c)

    # Scenario 2: Meet Charles first, then Richard
    scenario2.add(charles_start >= arrival_time + bayview_to_presidio)
    scenario2.add(richard_start >= charles_end + presidio_to_union_square)
    for c in s.assertions():
        scenario2.add(c)

    # Check which scenario works
    result = None
    if scenario1.check() == sat:
        result = scenario1.model()
        order = "Meet Richard first (9:17 AM), then Charles"
    elif scenario2.check() == sat:
        result = scenario2.model()
        order = "Meet Charles first (9:31 AM), then Richard"
    else:
        print("No feasible schedule found")
        return

    # Convert times to readable format
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d} AM" if h < 12 else f"{h-12}:{m:02d} PM"

    # Get meeting times
    rs = result.eval(richard_start).as_long()
    re = result.eval(richard_end).as_long()
    cs = result.eval(charles_start).as_long()
    ce = result.eval(charles_end).as_long()

    # Print solution
    print("SOLUTION:")
    print(f"Optimal meeting order: {order}")
    print(f"Richard meeting: {format_time(rs)} to {format_time(re)}")
    print(f"Charles meeting: {format_time(cs)} to {format_time(ce)}")

solve_scheduling()