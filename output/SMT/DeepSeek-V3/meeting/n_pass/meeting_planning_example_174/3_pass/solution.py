from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    # Starting at Nob Hill at 9:00 AM (540 minutes)
    start_time = 540

    # Friends' availability windows
    kenneth_start = 720  # 12:00 PM
    kenneth_end = 945    # 3:45 PM
    thomas_start = 1050  # 3:30 PM
    thomas_end = 1275    # 7:15 PM

    # Meeting durations
    kenneth_min_duration = 45
    thomas_min_duration = 75

    # Travel times (minutes)
    nob_to_mission = 13
    mission_to_pacific = 16

    # Meeting time variables
    k_meet_start = Int('k_meet_start')
    k_meet_end = Int('k_meet_end')
    t_meet_start = Int('t_meet_start')
    t_meet_end = Int('t_meet_end')

    # Constraints
    # Kenneth's meeting constraints
    s.add(k_meet_start >= kenneth_start)
    s.add(k_meet_end <= kenneth_end)
    s.add(k_meet_end == k_meet_start + kenneth_min_duration)

    # Thomas's meeting constraints
    s.add(t_meet_start >= thomas_start)
    s.add(t_meet_end <= thomas_end)
    s.add(t_meet_end == t_meet_start + thomas_min_duration)

    # Travel constraints
    # From Nob Hill to Mission District
    s.add(k_meet_start >= start_time + nob_to_mission)
    # From Mission District to Pacific Heights
    s.add(t_meet_start >= k_meet_end + mission_to_pacific)

    # Check for feasible solution
    if s.check() == sat:
        m = s.model()
        k_start = m.eval(k_meet_start).as_long()
        k_end = m.eval(k_meet_end).as_long()
        t_start = m.eval(t_meet_start).as_long()
        t_end = m.eval(t_meet_end).as_long()

        # Convert minutes to HH:MM format
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        print("SOLUTION:")
        print(f"1. Leave Nob Hill at 09:00")
        print(f"2. Arrive at Mission District at {format_time(start_time + nob_to_mission)}")
        print(f"3. Meet Kenneth from {format_time(k_start)} to {format_time(k_end)}")
        print(f"4. Travel to Pacific Heights, arriving at {format_time(k_end + mission_to_pacific)}")
        print(f"5. Meet Thomas from {format_time(t_start)} to {format_time(t_end)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()