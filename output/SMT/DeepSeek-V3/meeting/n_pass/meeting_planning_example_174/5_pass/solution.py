from z3 import *

def solve_scheduling():
    try:
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
            
            # Helper function to safely get integer values
            def get_time(var):
                val = m.eval(var)
                if is_int_value(val):
                    return val.as_long()
                return 0

            k_start = get_time(k_meet_start)
            k_end = get_time(k_meet_end)
            t_start = get_time(t_meet_start)
            t_end = get_time(t_meet_end)

            # Convert minutes to HH:MM format
            def format_time(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"

            # Build output string
            output = []
            output.append("SOLUTION:")
            output.append(f"1. Leave Nob Hill at 09:00")
            output.append(f"2. Arrive at Mission District at {format_time(start_time + nob_to_mission)}")
            output.append(f"3. Meet Kenneth from {format_time(k_start)} to {format_time(k_end)}")
            output.append(f"4. Travel to Pacific Heights, arriving at {format_time(k_end + mission_to_pacific)}")
            output.append(f"5. Meet Thomas from {format_time(t_start)} to {format_time(t_end)}")
            
            # Print the solution
            print('\n'.join(output))
        else:
            print("No feasible schedule found.")

    except Exception as e:
        print(f"An error occurred: {str(e)}")

solve_scheduling()