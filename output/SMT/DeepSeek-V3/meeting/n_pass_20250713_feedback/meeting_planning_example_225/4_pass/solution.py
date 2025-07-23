from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Jeffrey at Union Square: 3:00PM to 10:00PM, min 75 mins
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')

    # Sarah at North Beach: 4:00PM to 6:15PM, min 60 mins
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')

    # Convert all times to minutes since 9:00AM (540 minutes)
    # Constraints for Jeffrey
    s.add(jeffrey_start >= 15 * 60 - 540)  # 3:00PM is 15*60 = 900, 900-540=360
    s.add(jeffrey_end <= 22 * 60 - 540)    # 10:00PM is 22*60=1320, 1320-540=780
    s.add(jeffrey_end == jeffrey_start + 75)

    # Constraints for Sarah
    s.add(sarah_start >= 16 * 60 - 540)    # 4:00PM is 16*60=960, 960-540=420
    s.add(sarah_end <= 18 * 60 + 15 - 540) # 6:15PM is 18*60+15=1095, 1095-540=555
    s.add(sarah_end == sarah_start + 60)

    # We're only meeting Jeffrey and Sarah
    meet_jeffrey = 1
    meet_sarah = 1

    # Travel time from Union Square to North Beach is 10 minutes
    s.add(jeffrey_end + 10 <= sarah_start)

    # First meeting must be reachable from Sunset District
    # We're starting with Jeffrey at Union Square, travel time is 30 minutes
    s.add(jeffrey_start >= 30)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        print("Optimal schedule meets 2 friends:")
        jeff_s = model.evaluate(jeffrey_start).as_long() + 540
        jeff_e = model.evaluate(jeffrey_end).as_long() + 540
        print(f"Meet Jeffrey from {jeff_s//60}:{jeff_s%60:02d} to {jeff_e//60}:{jeff_e%60:02d}")
        
        sarah_s = model.evaluate(sarah_start).as_long() + 540
        sarah_e = model.evaluate(sarah_end).as_long() + 540
        print(f"Meet Sarah from {sarah_s//60}:{sarah_s%60:02d} to {sarah_e//60}:{sarah_e%60:02d}")
    else:
        print("No feasible schedule found that meets exactly two friends.")

solve_scheduling()