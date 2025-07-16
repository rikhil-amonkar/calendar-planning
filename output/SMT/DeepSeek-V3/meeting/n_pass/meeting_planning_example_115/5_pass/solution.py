from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since midnight
    # Starting at Richmond District at 9:00 AM (540 minutes)
    start_time = 540

    # Friends' availability windows
    carol_start = 690  # 11:30 AM
    carol_end = 900    # 3:00 PM
    jessica_start = 1050  # 3:30 PM
    jessica_end = 1125    # 4:45 PM

    # Meeting duration requirements
    min_carol = 60
    min_jessica = 45

    # Travel times between districts (in minutes)
    richmond_to_marina = 9
    marina_to_pacific = 7
    richmond_to_pacific = 10
    pacific_to_marina = 6
    marina_to_richmond = 11
    pacific_to_richmond = 12

    # Decision variables
    meet_carol = Bool('meet_carol')
    meet_jessica = Bool('meet_jessica')
    carol_meet_start = Int('carol_meet_start')
    carol_meet_end = Int('carol_meet_end')
    jessica_meet_start = Int('jessica_meet_start')
    jessica_meet_end = Int('jessica_meet_end')

    # Constraints for Carol
    s.add(Implies(meet_carol, carol_meet_start >= carol_start))
    s.add(Implies(meet_carol, carol_meet_end <= carol_end))
    s.add(Implies(meet_carol, carol_meet_end - carol_meet_start >= min_carol))

    # Constraints for Jessica
    s.add(Implies(meet_jessica, jessica_meet_start >= jessica_start))
    s.add(Implies(meet_jessica, jessica_meet_end <= jessica_end))
    s.add(Implies(meet_jessica, jessica_meet_end - jessica_meet_start >= min_jessica))

    # Starting point and travel constraints
    # Option 1: Meet Carol first, then Jessica
    s.add(Implies(And(meet_carol, meet_jessica),
          carol_meet_start >= start_time + richmond_to_marina))
    s.add(Implies(And(meet_carol, meet_jessica),
          jessica_meet_start >= carol_meet_end + marina_to_pacific))
    
    # Option 2: Meet Jessica first (not feasible due to time constraints)
    s.add(Not(And(meet_jessica, meet_carol,
                 jessica_meet_start >= start_time + richmond_to_pacific,
                 carol_meet_start >= jessica_meet_end + pacific_to_marina)))

    # Maximize number of meetings
    s.maximize(If(meet_carol, 1, 0) + If(meet_jessica, 1, 0))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        
        def minutes_to_time(mins):
            h = mins // 60
            m = mins % 60
            return f"{h}:{m:02d}"

        print("SOLUTION:")
        if is_true(m.eval(meet_carol)):
            print(f"Meet Carol from {minutes_to_time(m.eval(carol_meet_start).as_long())} to {minutes_to_time(m.eval(carol_meet_end).as_long())}")
        if is_true(m.eval(meet_jessica)):
            print(f"Meet Jessica from {minutes_to_time(m.eval(jessica_meet_start).as_long())} to {minutes_to_time(m.eval(jessica_meet_end).as_long())}")
    else:
        print("No feasible schedule found.")

solve_scheduling()