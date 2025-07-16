from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Kenneth's window: 12:00 PM (720) to 3:45 PM (945)
    kenneth_start_min = 720
    kenneth_end_min = 945
    # Thomas's window: 3:30 PM (1050) to 7:15 PM (1275)
    thomas_start_min = 1050
    thomas_end_min = 1275

    # Meeting durations in minutes
    kenneth_duration = 45
    thomas_duration = 75

    # Variables for meeting start times
    meet_kenneth_start = Int('meet_kenneth_start')
    meet_kenneth_end = Int('meet_kenneth_end')
    meet_thomas_start = Int('meet_thomas_start')
    meet_thomas_end = Int('meet_thomas_end')

    # Variables for travel times
    # Initial location: Nob Hill at 9:00 AM (540)
    # Possible sequences:
    # Option 1: Nob Hill -> Mission (Kenneth) -> Pacific (Thomas)
    # Option 2: Nob Hill -> Pacific (Thomas) -> Mission (Kenneth) -> but Thomas is only available after 3:30 PM, Kenneth before 3:45 PM. So this is impossible.
    # So only Option 1 is feasible.

    # Travel from Nob Hill to Mission District: 13 minutes
    travel_to_kenneth = 13
    # Travel from Mission District to Pacific Heights: 16 minutes
    travel_to_thomas = 16

    # Constraints for Kenneth's meeting
    s.add(meet_kenneth_start >= kenneth_start_min)
    s.add(meet_kenneth_end <= kenneth_end_min)
    s.add(meet_kenneth_end == meet_kenneth_start + kenneth_duration)

    # Constraints for Thomas's meeting
    s.add(meet_thomas_start >= thomas_start_min)
    s.add(meet_thomas_end <= thomas_end_min)
    s.add(meet_thomas_end == meet_thomas_start + thomas_duration)

    # Arrival at Mission District: must be after traveling from Nob Hill (540 + 13 = 553)
    s.add(meet_kenneth_start >= 540 + travel_to_kenneth)

    # Arrival at Pacific Heights: must be after meeting Kenneth and traveling to Pacific Heights
    s.add(meet_thomas_start >= meet_kenneth_end + travel_to_thomas)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        k_start = m.eval(meet_kenneth_start).as_long()
        k_end = m.eval(meet_kenneth_end).as_long()
        t_start = m.eval(meet_thomas_start).as_long()
        t_end = m.eval(meet_thomas_end).as_long()

        # Convert minutes back to time strings
        def min_to_time(minutes):
            h = (minutes // 60) % 24
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        k_start_time = min_to_time(k_start)
        k_end_time = min_to_time(k_end)
        t_start_time = min_to_time(t_start)
        t_end_time = min_to_time(t_end)

        print("SOLUTION:")
        print(f"Meet Kenneth at Mission District from {k_start_time} to {k_end_time}")
        print(f"Then travel to Pacific Heights and meet Thomas from {t_start_time} to {t_end_time}")
    else:
        print("No feasible schedule found.")

solve_scheduling()