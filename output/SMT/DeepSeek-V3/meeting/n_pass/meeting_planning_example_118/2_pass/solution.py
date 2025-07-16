from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Richard at Union Square
    richard_start = Int('richard_start')
    richard_end = Int('richard_end')
    
    # Meeting with Charles at Presidio
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Convert all times to minutes since midnight
    # Richard's availability: 8:45 AM (525) to 1:00 PM (780)
    richard_available_start = 525  # 8:45 AM in minutes
    richard_available_end = 780    # 1:00 PM in minutes
    
    # Charles's availability: 9:45 AM (585) to 1:00 PM (780)
    charles_available_start = 585  # 9:45 AM in minutes
    charles_available_end = 780    # 1:00 PM in minutes

    # Arrival time at Bayview: 9:00 AM (540)
    arrival_time = 540

    # Add constraints for Richard's meeting
    s.add(richard_start >= richard_available_start)
    s.add(richard_end <= richard_available_end)
    s.add(richard_end - richard_start >= 120)  # at least 120 minutes
    
    # Add constraints for Charles's meeting
    s.add(charles_start >= charles_available_start)
    s.add(charles_end <= charles_available_end)
    s.add(charles_end - charles_start >= 120)  # at least 120 minutes

    # Travel times (in minutes)
    bayview_to_union_square = 17
    bayview_to_presidio = 31
    union_square_to_presidio = 24
    presidio_to_union_square = 22

    # We need to consider the order of meetings and travel times
    # There are two possible orders:
    # 1. Meet Richard first, then Charles
    # 2. Meet Charles first, then Richard

    # Create two separate solvers for each scenario
    scenario1 = Solver()
    scenario2 = Solver()

    # Scenario 1: Richard first, then Charles
    scenario1.add(richard_start >= arrival_time + bayview_to_union_square)  # travel from Bayview to Union Square
    scenario1.add(charles_start >= richard_end + union_square_to_presidio)  # travel from Union Square to Presidio
    # Add all other constraints
    scenario1.add(richard_start >= richard_available_start)
    scenario1.add(richard_end <= richard_available_end)
    scenario1.add(richard_end - richard_start >= 120)
    scenario1.add(charles_start >= charles_available_start)
    scenario1.add(charles_end <= charles_available_end)
    scenario1.add(charles_end - charles_start >= 120)

    # Scenario 2: Charles first, then Richard
    scenario2.add(charles_start >= arrival_time + bayview_to_presidio)  # travel from Bayview to Presidio
    scenario2.add(richard_start >= charles_end + presidio_to_union_square)  # travel from Presidio to Union Square
    # Add all other constraints
    scenario2.add(richard_start >= richard_available_start)
    scenario2.add(richard_end <= richard_available_end)
    scenario2.add(richard_end - richard_start >= 120)
    scenario2.add(charles_start >= charles_available_start)
    scenario2.add(charles_end <= charles_available_end)
    scenario2.add(charles_end - charles_start >= 120)

    # Check which scenario is feasible
    feasible_scenario = None
    model = None

    if scenario1.check() == sat:
        feasible_scenario = 1
        model = scenario1.model()
    elif scenario2.check() == sat:
        feasible_scenario = 2
        model = scenario2.model()
    else:
        print("No feasible schedule found.")
        return

    # Extract the times from the model
    richard_start_val = model.evaluate(richard_start).as_long()
    richard_end_val = model.evaluate(richard_end).as_long()
    charles_start_val = model.evaluate(charles_start).as_long()
    charles_end_val = model.evaluate(charles_end).as_long()

    # Convert times back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    if feasible_scenario == 1:
        print("Feasible schedule: Meet Richard first, then Charles")
    else:
        print("Feasible schedule: Meet Charles first, then Richard")

    print(f"Meet Richard from {minutes_to_time(richard_start_val)} to {minutes_to_time(richard_end_val)}")
    print(f"Meet Charles from {minutes_to_time(charles_start_val)} to {minutes_to_time(charles_end_val)}")

solve_scheduling()