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

    # Brian at Alamo Square: 4:00PM to 5:30PM, min 75 mins
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')

    # Convert all times to minutes since 9:00AM (540 minutes)
    # Constraints for Jeffrey
    s.add(jeffrey_start >= 15 * 60 - 540)  # 3:00PM is 15*60 = 900, 900-540=360
    s.add(jeffrey_end <= 22 * 60 - 540)    # 10:00PM is 22*60=1320, 1320-540=780
    s.add(jeffrey_end == jeffrey_start + 75)

    # Constraints for Sarah
    s.add(sarah_start >= 16 * 60 - 540)    # 4:00PM is 16*60=960, 960-540=420
    s.add(sarah_end <= 18 * 60 + 15 - 540) # 6:15PM is 18*60+15=1095, 1095-540=555
    s.add(sarah_end == sarah_start + 60)

    # Constraints for Brian
    s.add(brian_start >= 16 * 60 - 540)    # 4:00PM is 16*60=960, 960-540=420
    s.add(brian_end <= 17 * 60 + 30 - 540) # 5:30PM is 17*60+30=1050, 1050-540=510
    s.add(brian_end == brian_start + 75)

    # Define variables to indicate whether each meeting is scheduled
    meet_jeffrey = Int('meet_jeffrey')
    meet_sarah = Int('meet_sarah')
    meet_brian = Int('meet_brian')

    s.add(Or(meet_jeffrey == 0, meet_jeffrey == 1))
    s.add(Or(meet_sarah == 0, meet_sarah == 1))
    s.add(Or(meet_brian == 0, meet_brian == 1))

    # If a meeting is scheduled, its start and end times must be within constraints
    s.add(Implies(meet_jeffrey == 1, And(jeffrey_start >= 360, jeffrey_end <= 780)))
    s.add(Implies(meet_sarah == 1, And(sarah_start >= 420, sarah_end <= 555)))
    s.add(Implies(meet_brian == 1, And(brian_start >= 420, brian_end <= 510)))

    # Define the order of meetings and travel times
    # We start at Sunset District at time 0 (9:00AM)
    # We need to model the sequence of meetings and travel times

    # Possible sequences:
    # 1. Jeffrey -> Sarah -> Brian or other permutations
    # But given the time windows, some sequences may not be possible

    # To model this, we'll assume that we can meet at most two friends due to overlapping time windows
    # Let's try to meet Jeffrey and Sarah, or Jeffrey and Brian, or Sarah and Brian

    # We'll maximize the sum of meet_jeffrey, meet_sarah, meet_brian
    total_met = meet_jeffrey + meet_sarah + meet_brian

    # Add constraints to ensure travel times are respected between meetings
    # For example, if we meet Jeffrey and then Sarah:
    # jeffrey_end + travel_time(Union Square -> North Beach) <= sarah_start
    # travel_time(Union Square -> North Beach) is 10 minutes
    s.add(Implies(And(meet_jeffrey == 1, meet_sarah == 1), jeffrey_end + 10 <= sarah_start))
    # Similarly for other combinations
    s.add(Implies(And(meet_jeffrey == 1, meet_brian == 1), jeffrey_end + 15 <= brian_start))
    s.add(Implies(And(meet_sarah == 1, meet_brian == 1), sarah_end + 15 <= brian_start))
    s.add(Implies(And(meet_brian == 1, meet_sarah == 1), brian_end + 15 <= sarah_start))
    s.add(Implies(And(meet_brian == 1, meet_jeffrey == 1), brian_end + 14 <= jeffrey_start))
    s.add(Implies(And(meet_sarah == 1, meet_jeffrey == 1), sarah_end + 7 <= jeffrey_start))

    # Also, the first meeting must be reachable from Sunset District
    # Travel times from Sunset District:
    # Sunset to North Beach: 29
    # Sunset to Union Square: 30
    # Sunset to Alamo Square: 17
    s.add(Implies(meet_jeffrey == 1, And(Or(meet_sarah == 0, meet_brian == 0)), jeffrey_start >= 30))
    s.add(Implies(meet_sarah == 1, And(Or(meet_jeffrey == 0, meet_brian == 0)), sarah_start >= 29))
    s.add(Implies(meet_brian == 1, And(Or(meet_jeffrey == 0, meet_sarah == 0)), brian_start >= 17))

    # Maximize the number of friends met
    max_met = 0
    model = None
    s.push()
    s.add(total_met >= 2)
    if s.check() == sat:
        model = s.model()
        max_met = model.evaluate(total_met).as_long()
    else:
        s.pop()
        s.add(total_met >= 1)
        if s.check() == sat:
            model = s.model()
            max_met = model.evaluate(total_met).as_long()

    if model is None:
        print("No feasible schedule found.")
        return

    print("Optimal schedule meets", max_met, "friends:")
    if model.evaluate(meet_jeffrey).as_long() == 1:
        jeff_s = model.evaluate(jeffrey_start).as_long() + 540
        jeff_e = model.evaluate(jeffrey_end).as_long() + 540
        print(f"Meet Jeffrey from {jeff_s//60}:{jeff_s%60:02d} to {jeff_e//60}:{jeff_e%60:02d}")
    if model.evaluate(meet_sarah).as_long() == 1:
        sarah_s = model.evaluate(sarah_start).as_long() + 540
        sarah_e = model.evaluate(sarah_end).as_long() + 540
        print(f"Meet Sarah from {sarah_s//60}:{sarah_s%60:02d} to {sarah_e//60}:{sarah_e%60:02d}")
    if model.evaluate(meet_brian).as_long() == 1:
        brian_s = model.evaluate(brian_start).as_long() + 540
        brian_e = model.evaluate(brian_end).as_long() + 540
        print(f"Meet Brian from {brian_s//60}:{brian_s%60:02d} to {brian_e//60}:{brian_e%60:02d}")

solve_scheduling()