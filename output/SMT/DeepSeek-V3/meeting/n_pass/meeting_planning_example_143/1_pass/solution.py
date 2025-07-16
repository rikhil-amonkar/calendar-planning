from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Constants
    karen_start_available = (18 * 60 + 45) - 540  # 6:45 PM is 18:45, 9:00 AM is 540 minutes since midnight
    karen_end_available = (20 * 60 + 15) - 540    # 8:15 PM is 20:15
    mark_start_available = (13 * 60 + 0) - 540    # 1:00 PM is 13:00
    mark_end_available = (17 * 60 + 45) - 540     # 5:45 PM is 17:45

    # Travel times in minutes
    travel_NB_to_PH = 8
    travel_NB_to_EM = 6
    travel_PH_to_NB = 9
    travel_PH_to_EM = 10
    travel_EM_to_NB = 5
    travel_EM_to_PH = 11

    # Variables for meeting start and end times (in minutes since 9:00 AM)
    meet_mark_start = Int('meet_mark_start')
    meet_mark_end = Int('meet_mark_end')
    meet_karen_start = Int('meet_karen_start')
    meet_karen_end = Int('meet_karen_end')

    # Variables to track the order of meetings
    meet_mark_first = Bool('meet_mark_first')

    # Constraints for Mark's meeting
    s.add(meet_mark_start >= mark_start_available)
    s.add(meet_mark_end <= mark_end_available)
    s.add(meet_mark_end - meet_mark_start >= 120)  # at least 120 minutes

    # Constraints for Karen's meeting
    s.add(meet_karen_start >= karen_start_available)
    s.add(meet_karen_end <= karen_end_available)
    s.add(meet_karen_end - meet_karen_start >= 90)  # at least 90 minutes

    # Initial location is North Beach at time 0 (9:00 AM)
    # We need to model the sequence of meetings and travel times

    # Option 1: Meet Mark first, then Karen
    s.add(Implies(meet_mark_first,
                  And(
                      meet_mark_start >= travel_NB_to_EM,  # time to travel to Embarcadero
                      meet_karen_start >= meet_mark_end + travel_EM_to_PH  # time to travel to Pacific Heights
                  )))

    # Option 2: Meet Karen first, then Mark
    s.add(Implies(Not(meet_mark_first),
                  And(
                      meet_karen_start >= travel_NB_to_PH,  # time to travel to Pacific Heights
                      meet_mark_start >= meet_karen_end + travel_PH_to_EM  # time to travel to Embarcadero
                  )))

    # Ensure that Mark's meeting ends before Karen's starts if meeting Mark first, and vice versa
    s.add(Or(
        And(meet_mark_first, meet_karen_start >= meet_mark_end + travel_EM_to_PH),
        And(Not(meet_mark_first), meet_mark_start >= meet_karen_end + travel_PH_to_EM)
    ))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        mark_start = m.evaluate(meet_mark_start).as_long()
        mark_end = m.evaluate(meet_mark_end).as_long()
        karen_start = m.evaluate(meet_karen_start).as_long()
        karen_end = m.evaluate(meet_karen_end).as_long()
        is_mark_first = m.evaluate(meet_mark_first)

        # Convert times back to hours and minutes since 9:00 AM
        def to_time_str(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours}:{mins:02d}"

        print("SOLUTION:")
        print(f"Meet Mark first: {is_mark_first}")
        print(f"Meet Mark from {to_time_str(mark_start)} to {to_time_str(mark_end)}")
        print(f"Meet Karen from {to_time_str(karen_start)} to {to_time_str(karen_end)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()