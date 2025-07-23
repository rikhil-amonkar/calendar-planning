from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since 9:00AM (540 minutes since midnight)
    # Emily's availability: 4:00PM (16:00) to 5:15PM (17:15) -> 960 to 1035 minutes
    emily_start_min = 960
    emily_end_min = 1035
    # Margaret's availability: 7:00PM (19:00) to 9:00PM (21:00) -> 1140 to 1260 minutes
    margaret_start_min = 1140
    margaret_end_min = 1260

    # Meeting durations in minutes
    emily_duration = 45
    margaret_duration = 120

    # Variables for meeting start times
    emily_meet_start = Int('emily_meet_start')
    margaret_meet_start = Int('margaret_meet_start')

    # Constraints for Emily's meeting
    s.add(emily_meet_start >= emily_start_min)
    s.add(emily_meet_start + emily_duration <= emily_end_min)

    # Constraints for Margaret's meeting
    s.add(margaret_meet_start >= margaret_start_min)
    s.add(margaret_meet_start + margaret_duration <= margaret_end_min)

    # Travel times (in minutes)
    # From North Beach to Union Square: 7
    # From North Beach to Russian Hill: 4
    # From Union Square to Russian Hill: 13
    # From Russian Hill to Union Square: 11
    # From Union Square to North Beach: 10
    # From Russian Hill to North Beach: 5

    # We start at North Beach at 9:00AM (540 minutes)
    current_time = 540
    current_location = 'North Beach'

    # Determine the order of meetings
    # Option 1: Meet Emily first, then Margaret
    # Option 2: Meet Margaret first, then Emily
    # We'll explore both options and see which one is feasible

    # Option 1: Emily first, then Margaret
    # Travel from North Beach to Union Square: 7 minutes
    travel1 = 7
    meet_emily_start1 = current_time + travel1
    meet_emily_end1 = meet_emily_start1 + emily_duration
    # Travel from Union Square to Russian Hill: 13 minutes
    travel2 = 13
    meet_margaret_start1 = meet_emily_end1 + travel2
    meet_margaret_end1 = meet_margaret_start1 + margaret_duration

    # Check if this schedule fits
    s.push()
    s.add(emily_meet_start == meet_emily_start1)
    s.add(margaret_meet_start == meet_margaret_start1)
    if s.check() == sat:
        print("Option 1 is feasible:")
        m = s.model()
        print(f"Meet Emily from {m[emily_meet_start]} to {m[emily_meet_start].as_long() + emily_duration}")
        print(f"Meet Margaret from {m[margaret_meet_start]} to {m[margaret_meet_start].as_long() + margaret_duration}")
        s.pop()
        return

    s.pop()

    # Option 2: Margaret first, then Emily
    # Travel from North Beach to Russian Hill: 4 minutes
    travel1 = 4
    meet_margaret_start2 = current_time + travel1
    meet_margaret_end2 = meet_margaret_start2 + margaret_duration
    # Travel from Russian Hill to Union Square: 11 minutes
    travel2 = 11
    meet_emily_start2 = meet_margaret_end2 + travel2
    meet_emily_end2 = meet_emily_start2 + emily_duration

    s.push()
    s.add(emily_meet_start == meet_emily_start2)
    s.add(margaret_meet_start == meet_margaret_start2)
    if s.check() == sat:
        print("Option 2 is feasible:")
        m = s.model()
        print(f"Meet Margaret from {m[margaret_meet_start]} to {m[margaret_meet_start].as_long() + margaret_duration}")
        print(f"Meet Emily from {m[emily_meet_start]} to {m[emily_meet_start].as_long() + emily_duration}")
        s.pop()
        return

    s.pop()

    print("No feasible schedule found.")

solve_scheduling()