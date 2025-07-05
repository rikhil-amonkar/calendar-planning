from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    castro_arrival = 540  # 9:00 AM is 540 minutes

    # Meeting windows in minutes since midnight
    emily_start = 11 * 60 + 45  # 11:45 AM
    emily_end = 15 * 60 + 15    # 3:15 PM
    barbara_start = 16 * 60 + 45  # 4:45 PM
    barbara_end = 18 * 60 + 15    # 6:15 PM
    william_start = 17 * 60 + 15  # 5:15 PM
    william_end = 19 * 60         # 7:00 PM

    # Minimum meeting durations in minutes
    emily_min_duration = 105
    barbara_min_duration = 60
    william_min_duration = 105

    # Travel times in minutes
    travel = {
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Chinatown'): 20,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Chinatown'): 16,
        ('Union Square', 'The Castro'): 19,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Union Square'): 7,
    }

    # Variables for meeting start and end times
    emily_meet_start = Int('emily_meet_start')
    emily_meet_end = Int('emily_meet_end')
    barbara_meet_start = Int('barbara_meet_start')
    barbara_meet_end = Int('barbara_meet_end')
    william_meet_start = Int('william_meet_start')
    william_meet_end = Int('william_meet_end')

    # Variables to track travel times
    travel1 = Int('travel1')  # Castro to Alamo Square (for Emily)
    travel2 = Int('travel2')  # Alamo Square to next location (Union Square or Chinatown)
    travel3 = Int('travel3')  # Next location to final location

    # Constraints for Emily's meeting
    s.add(emily_meet_start >= emily_start)
    s.add(emily_meet_end <= emily_end)
    s.add(emily_meet_end - emily_meet_start >= emily_min_duration)
    s.add(emily_meet_start >= castro_arrival + travel[('The Castro', 'Alamo Square')])

    # Constraints for Barbara's meeting
    s.add(barbara_meet_start >= barbara_start)
    s.add(barbara_meet_end <= barbara_end)
    s.add(barbara_meet_end - barbara_meet_start >= barbara_min_duration)

    # Constraints for William's meeting
    s.add(william_meet_start >= william_start)
    s.add(william_meet_end <= william_end)
    s.add(william_meet_end - william_meet_start >= william_min_duration)

    # Define possible sequences of meetings
    # Option 1: Emily -> Barbara -> William
    # Travel from Alamo Square to Union Square, then to Chinatown
    s.push()
    s.add(travel1 == travel[('The Castro', 'Alamo Square')])
    s.add(travel2 == travel[('Alamo Square', 'Union Square')])
    s.add(travel3 == travel[('Union Square', 'Chinatown')])
    s.add(barbara_meet_start >= emily_meet_end + travel2)
    s.add(william_meet_start >= barbara_meet_end + travel3)
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        print(f"Emily: {m[emily_meet_start]} to {m[emily_meet_end]}")
        print(f"Barbara: {m[barbara_meet_start]} to {m[barbara_meet_end]}")
        print(f"William: {m[william_meet_start]} to {m[william_meet_end]}")
        return
    s.pop()

    # Option 2: Emily -> William -> Barbara
    # Travel from Alamo Square to Chinatown, then to Union Square
    s.push()
    s.add(travel1 == travel[('The Castro', 'Alamo Square')])
    s.add(travel2 == travel[('Alamo Square', 'Chinatown')])
    s.add(travel3 == travel[('Chinatown', 'Union Square')])
    s.add(william_meet_start >= emily_meet_end + travel2)
    s.add(barbara_meet_start >= william_meet_end + travel3)
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        print(f"Emily: {m[emily_meet_start]} to {m[emily_meet_end]}")
        print(f"William: {m[william_meet_start]} to {m[william_meet_end]}")
        print(f"Barbara: {m[barbara_meet_start]} to {m[barbara_meet_end]}")
        return
    s.pop()

    # Option 3: Barbara -> William (but Emily must be met first)
    # Not possible since Emily's window is earlier

    # If no feasible schedule found
    print("No feasible schedule found that meets all constraints.")

solve_scheduling()