from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define all time points in minutes since 9:00 AM
    steph_start = Int('steph_start')
    steph_end = Int('steph_end')
    john_start = Int('john_start')
    john_end = Int('john_end')

    # Travel times in minutes
    EMB_TO_FIN = 5
    FIN_TO_ALAMO = 17
    EMB_TO_ALAMO = 19
    ALAMO_TO_EMB = 17

    # Friend availability windows (minutes since 9:00 AM)
    STEPH_AVAIL_START = -45  # 8:15 AM
    STEPH_AVAIL_END = 150    # 11:30 AM
    JOHN_AVAIL_START = 75    # 10:15 AM
    JOHN_AVAIL_END = 705     # 8:45 PM

    # Meeting duration constraints
    MIN_STEPH_TIME = 90
    MIN_JOHN_TIME = 30

    # Basic meeting constraints
    s.add(steph_start >= 0)  # Can't start before 9:00 AM
    s.add(steph_end <= STEPH_AVAIL_END)
    s.add(steph_end - steph_start >= MIN_STEPH_TIME)
    
    s.add(john_start >= JOHN_AVAIL_START)
    s.add(john_end <= JOHN_AVAIL_END)
    s.add(john_end - john_start >= MIN_JOHN_TIME)

    # Define meeting order options
    meet_steph_first = And(
        steph_start >= EMB_TO_FIN,
        john_start >= steph_end + FIN_TO_ALAMO
    )

    meet_john_first = And(
        john_start >= EMB_TO_ALAMO,
        steph_start >= john_end + FIN_TO_ALAMO
    )

    s.add(Or(meet_steph_first, meet_john_first))

    # Maximize total meeting time
    total_time = (steph_end - steph_start) + (john_end - john_start)
    s.maximize(total_time)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        st_start = m.eval(steph_start).as_long()
        st_end = m.eval(steph_end).as_long()
        j_start = m.eval(john_start).as_long()
        j_end = m.eval(john_end).as_long()

        # Helper function to format time
        def format_time(mins):
            total_mins = 9 * 60 + mins
            h = total_mins // 60
            m = total_mins % 60
            ampm = "AM" if h < 12 else "PM"
            h = h if h <= 12 else h - 12
            return f"{h}:{m:02d} {ampm}"

        print("\nOptimal Schedule:")
        print(f"• Meet Stephanie: {format_time(st_start)} to {format_time(st_end)}")
        print(f"• Meet John: {format_time(j_start)} to {format_time(j_end)}")
        print(f"\nTotal meeting time: {st_end - st_start + j_end - j_start} minutes")

        # Show travel plan
        if m.eval(meet_steph_first):
            print("\nTravel Plan:")
            print(f"1. Start at Embarcadero at 9:00 AM")
            print(f"2. Travel to Financial District (5 mins), arrive at {format_time(EMB_TO_FIN)}")
            print(f"3. Meet Stephanie until {format_time(st_end)}")
            print(f"4. Travel to Alamo Square (17 mins), arrive at {format_time(st_end + FIN_TO_ALAMO)}")
            print(f"5. Meet John until {format_time(j_end)}")
        else:
            print("\nTravel Plan:")
            print(f"1. Start at Embarcadero at 9:00 AM")
            print(f"2. Travel to Alamo Square (19 mins), arrive at {format_time(EMB_TO_ALAMO)}")
            print(f"3. Meet John until {format_time(j_end)}")
            print(f"4. Travel to Financial District (17 mins), arrive at {format_time(j_end + FIN_TO_ALAMO)}")
            print(f"5. Meet Stephanie until {format_time(st_end)}")
    else:
        print("No valid schedule found that meets all constraints.")

solve_scheduling()