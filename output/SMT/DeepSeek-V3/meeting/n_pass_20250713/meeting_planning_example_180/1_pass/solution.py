from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # James is available at Mission District from 12:45 PM (765 minutes) to 2:00 PM (840 minutes)
    james_start_avail = 765  # 12:45 PM in minutes since midnight
    james_end_avail = 840     # 2:00 PM in minutes since midnight
    # Robert is available at The Castro from 12:45 PM (765) to 3:15 PM (915 minutes)
    robert_start_avail = 765  # 12:45 PM
    robert_end_avail = 915     # 3:15 PM

    # Meeting durations in minutes
    james_min_duration = 75
    robert_min_duration = 30

    # Travel times (in minutes)
    # From North Beach to Mission District: 18
    nb_to_md = 18
    # From North Beach to The Castro: 22
    nb_to_castro = 22
    # From Mission District to The Castro: 7
    md_to_castro = 7
    # From The Castro to Mission District: 7
    castro_to_md = 7
    # From Mission District to North Beach: 17
    md_to_nb = 17
    # From The Castro to North Beach: 20
    castro_to_nb = 20

    # Variables for meeting start times and durations
    # We need to decide the order of meetings: James first or Robert first, or only one.

    # Possible scenarios:
    # 1. Meet James first, then Robert
    # 2. Meet Robert first, then James
    # 3. Meet only James or only Robert (but the problem asks to meet as many as possible, so likely both)

    # Scenario 1: James first, then Robert
    # Variables for this scenario
    james_start1 = Int('james_start1')
    james_end1 = Int('james_end1')
    travel_to_robert1 = Int('travel_to_robert1')
    robert_start1 = Int('robert_start1')
    robert_end1 = Int('robert_end1')

    # Constraints for scenario 1
    scenario1 = And(
        james_start1 >= james_start_avail,
        james_end1 <= james_end_avail,
        james_end1 == james_start1 + james_min_duration,
        travel_to_robert1 == md_to_castro,
        robert_start1 == james_end1 + travel_to_robert1,
        robert_start1 >= robert_start_avail,
        robert_end1 == robert_start1 + robert_min_duration,
        robert_end1 <= robert_end_avail,
        # Initial travel from North Beach to Mission District to meet James
        james_start1 >= 540 + nb_to_md  # 9:00 AM is 540, plus travel time
    )

    # Scenario 2: Robert first, then James
    # Variables for this scenario
    robert_start2 = Int('robert_start2')
    robert_end2 = Int('robert_end2')
    travel_to_james2 = Int('travel_to_james2')
    james_start2 = Int('james_start2')
    james_end2 = Int('james_end2')

    # Constraints for scenario 2
    scenario2 = And(
        robert_start2 >= robert_start_avail,
        robert_end2 <= robert_end_avail,
        robert_end2 == robert_start2 + robert_min_duration,
        travel_to_james2 == castro_to_md,
        james_start2 == robert_end2 + travel_to_james2,
        james_start2 >= james_start_avail,
        james_end2 == james_start2 + james_min_duration,
        james_end2 <= james_end_avail,
        # Initial travel from North Beach to The Castro to meet Robert
        robert_start2 >= 540 + nb_to_castro
    )

    # Check if either scenario is possible
    s.push()
    s.add(scenario1)
    if s.check() == sat:
        m = s.model()
        print("Scenario 1 (James first, then Robert) is feasible.")
        print(f"Meet James from {m[james_start1].as_long()} minutes (since midnight) to {m[james_end1].as_long()} minutes.")
        print(f"Then travel to Robert (takes {md_to_castro} minutes), meet from {m[robert_start1].as_long()} to {m[robert_end1].as_long()}.")
        s.pop()
        return

    s.pop()
    s.push()
    s.add(scenario2)
    if s.check() == sat:
        m = s.model()
        print("Scenario 2 (Robert first, then James) is feasible.")
        print(f"Meet Robert from {m[robert_start2].as_long()} minutes (since midnight) to {m[robert_end2].as_long()} minutes.")
        print(f"Then travel to James (takes {castro_to_md} minutes), meet from {m[james_start2].as_long()} to {m[james_end2].as_long()}.")
        s.pop()
        return

    s.pop()
    print("No feasible schedule to meet both friends. Trying to meet only one...")

    # Try meeting only James
    s.push()
    james_start_only = Int('james_start_only')
    james_end_only = Int('james_end_only')
    s.add(
        james_start_only >= james_start_avail,
        james_end_only <= james_end_avail,
        james_end_only == james_start_only + james_min_duration,
        james_start_only >= 540 + nb_to_md
    )
    if s.check() == sat:
        m = s.model()
        print("Only meeting James is feasible.")
        print(f"Meet James from {m[james_start_only].as_long()} to {m[james_end_only].as_long()}.")
        s.pop()
        return

    s.pop()
    # Try meeting only Robert
    s.push()
    robert_start_only = Int('robert_start_only')
    robert_end_only = Int('robert_end_only')
    s.add(
        robert_start_only >= robert_start_avail,
        robert_end_only <= robert_end_avail,
        robert_end_only == robert_start_only + robert_min_duration,
        robert_start_only >= 540 + nb_to_castro
    )
    if s.check() == sat:
        m = s.model()
        print("Only meeting Robert is feasible.")
        print(f"Meet Robert from {m[robert_start_only].as_long()} to {m[robert_end_only].as_long()}.")
        s.pop()
        return

    s.pop()
    print("No feasible schedule to meet any friend under the constraints.")

def main():
    solve_scheduling()

if __name__ == "__main__":
    main()