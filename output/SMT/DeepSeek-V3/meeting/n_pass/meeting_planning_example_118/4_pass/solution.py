from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting times (in minutes since midnight)
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Define time constants (in minutes since midnight)
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

    # Meeting duration constraints
    s.add(richard_end - richard_start >= 120)
    s.add(charles_end - charles_start >= 120)

    # Availability windows
    s.add(richard_start >= richard_available_start)
    s.add(richard_end <= richard_available_end)
    s.add(charles_start >= charles_available_start)
    s.add(charles_end <= charles_available_end)

    # Create two scenarios for meeting order
    scenario1 = Solver()
    scenario2 = Solver()

    # Scenario 1: Richard first, then Charles
    scenario1.add(richard_start >= arrival_time + bayview_to_union_square)
    scenario1.add(charles_start >= richard_end + union_square_to_presidio)
    # Copy all other constraints
    for c in s.assertions():
        scenario1.add(c)

    # Scenario 2: Charles first, then Richard
    scenario2.add(charles_start >= arrival_time + bayview_to_presidio)
    scenario2.add(richard_start >= charles_end + presidio_to_union_square)
    # Copy all other constraints
    for c in s.assertions():
        scenario2.add(c)

    # Check which scenario is feasible
    if scenario1.check() == sat:
        model = scenario1.model()
        order = "Richard first, then Charles"
    elif scenario2.check() == sat:
        model = scenario2.model()
        order = "Charles first, then Richard"
    else:
        print("No feasible schedule found")
        return

    # Convert times to readable format
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"

    # Get meeting times from model
    rs = model.eval(richard_start).as_long()
    re = model.eval(richard_end).as_long()
    cs = model.eval(charles_start).as_long()
    ce = model.eval(charles_end).as_long()

    # Print results
    print("SOLUTION:")
    print(f"Meeting order: {order}")
    print(f"Meet Richard: {format_time(rs)} to {format_time(re)}")
    print(f"Meet Charles: {format_time(cs)} to {format_time(ce)}")

solve_scheduling()