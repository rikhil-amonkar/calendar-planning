from z3 import *
from datetime import datetime, timedelta

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Base time (9:00 AM)
    base_time = datetime(2023, 1, 1, 9, 0)

    # Define all time points as minutes since base time
    steph_start = Int('steph_start')
    steph_end = Int('steph_end')
    john_start = Int('john_start')
    john_end = Int('john_end')

    # Travel times in minutes
    EMB_TO_FIN = 5
    FIN_TO_ALAMO = 17
    EMB_TO_ALAMO = 19
    ALAMO_TO_EMB = 17

    # Friend availability windows (minutes since base time)
    STEPH_AVAIL_START = -45  # 8:15 AM
    STEPH_AVAIL_END = 150    # 11:30 AM
    JOHN_AVAIL_START = 75    # 10:15 AM
    JOHN_AVAIL_END = 705     # 8:45 PM

    # Meeting duration constraints
    MIN_STEPH_TIME = 90
    MIN_JOHN_TIME = 30

    # Basic constraints
    s.add(steph_start >= 0)  # Can't start before 9:00 AM
    s.add(steph_end <= STEPH_AVAIL_END)
    s.add(steph_end - steph_start >= MIN_STEPH_TIME)
    
    s.add(john_start >= JOHN_AVAIL_START)
    s.add(john_end <= JOHN_AVAIL_END)
    s.add(john_end - john_start >= MIN_JOHN_TIME)

    # Meeting order options
    option1 = And(
        steph_start >= EMB_TO_FIN,
        john_start >= steph_end + FIN_TO_ALAMO
    )

    option2 = And(
        john_start >= EMB_TO_ALAMO,
        steph_start >= john_end + FIN_TO_ALAMO
    )

    s.add(Or(option1, option2))

    # Maximize total meeting time
    total_time = (steph_end - steph_start) + (john_end - john_start)
    s.maximize(total_time)

    # Check for solution
    result = s.check()
    if result == sat:
        m = s.model()
        st_start = m.eval(steph_start).as_long()
        st_end = m.eval(steph_end).as_long()
        j_start = m.eval(john_start).as_long()
        j_end = m.eval(john_end).as_long()

        # Convert minutes to datetime objects
        def mins_to_time(mins):
            return base_time + timedelta(minutes=mins)

        print("\nOptimal Schedule Found:")
        print(f"Meet Stephanie: {mins_to_time(st_start).strftime('%I:%M %p')} to {mins_to_time(st_end).strftime('%I:%M %p')}")
        print(f"Meet John: {mins_to_time(j_start).strftime('%I:%M %p')} to {mins_to_time(j_end).strftime('%I:%M %p')}")
        print(f"\nTotal meeting time: {st_end - st_start + j_end - j_start} minutes")

        # Show travel plan
        if is_true(m.eval(option1)):
            print("\nTravel Plan:")
            print(f"1. Start at Embarcadero at 9:00 AM")
            print(f"2. Arrive at Financial District at {mins_to_time(EMB_TO_FIN).strftime('%I:%M %p')}")
            print(f"3. Leave Financial District at {mins_to_time(st_end).strftime('%I:%M %p')}")
            print(f"4. Arrive at Alamo Square at {mins_to_time(st_end + FIN_TO_ALAMO).strftime('%I:%M %p')}")
        else:
            print("\nTravel Plan:")
            print(f"1. Start at Embarcadero at 9:00 AM")
            print(f"2. Arrive at Alamo Square at {mins_to_time(EMB_TO_ALAMO).strftime('%I:%M %p')}")
            print(f"3. Leave Alamo Square at {mins_to_time(j_end).strftime('%I:%M %p')}")
            print(f"4. Arrive at Financial District at {mins_to_time(j_end + FIN_TO_ALAMO).strftime('%I:%M %p')}")
    elif result == unsat:
        print("No valid schedule found that meets all constraints.")
    else:
        print("The solver could not determine a solution (unknown)")

solve_scheduling()