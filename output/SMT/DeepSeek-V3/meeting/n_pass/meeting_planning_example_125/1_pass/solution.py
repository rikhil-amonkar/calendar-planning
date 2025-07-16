from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Variables
    # Meeting Stephanie in Financial District
    meet_stephanie_start = Int('meet_stephanie_start')
    meet_stephanie_end = Int('meet_stephanie_end')
    # Meeting John in Alamo Square
    meet_john_start = Int('meet_john_start')
    meet_john_end = Int('meet_john_end')
    # Travel times (in minutes since 9:00 AM)
    travel_to_financial = 5  # Embarcadero to Financial District
    travel_to_alamo_from_financial = 17  # Financial District to Alamo Square
    travel_to_alamo_from_embarcadero = 19  # Embarcadero to Alamo Square
    travel_back_to_embarcadero = 17  # Alamo Square to Embarcadero

    # Convert friend availability to minutes since 9:00 AM
    stephanie_start = (8 * 60 + 15) - (9 * 60)  # 8:15 AM is -45 minutes from 9:00 AM
    stephanie_end = (11 * 60 + 30) - (9 * 60)    # 11:30 AM is 150 minutes from 9:00 AM
    john_start = (10 * 60 + 15) - (9 * 60)       # 10:15 AM is 75 minutes from 9:00 AM
    john_end = (20 * 60 + 45) - (9 * 60)         # 8:45 PM is 705 minutes from 9:00 AM

    # Constraints for Stephanie
    s.add(meet_stephanie_start >= stephanie_start)  # Stephanie is available from 8:15 AM (but we start at 9:00 AM)
    s.add(meet_stephanie_start >= 0)  # We can't start before 9:00 AM
    s.add(meet_stephanie_end <= stephanie_end)
    s.add(meet_stephanie_end - meet_stephanie_start >= 90)  # Minimum 90 minutes with Stephanie

    # Constraints for John
    s.add(meet_john_start >= john_start)
    s.add(meet_john_end <= john_end)
    s.add(meet_john_end - meet_john_start >= 30)  # Minimum 30 minutes with John

    # Travel constraints
    # Option 1: Meet Stephanie first, then John
    # Travel from Embarcadero to Financial District (5 mins), then Financial to Alamo (17 mins)
    option1 = And(
        meet_stephanie_start >= travel_to_financial,  # Start meeting Stephanie after travel
        meet_john_start >= meet_stephanie_end + travel_to_alamo_from_financial
    )
    # Option 2: Meet John first, then Stephanie
    # Travel from Embarcadero to Alamo Square (19 mins), then Alamo to Financial (17 mins)
    option2 = And(
        meet_john_start >= travel_to_alamo_from_embarcadero,
        meet_stephanie_start >= meet_john_end + travel_to_alamo_from_financial
    )
    # Only one option can be true
    s.add(Or(option1, option2))

    # Maximize total time with friends
    total_time = (meet_stephanie_end - meet_stephanie_start) + (meet_john_end - meet_john_start)
    s.maximize(total_time)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        steph_start = m.eval(meet_stephanie_start).as_long()
        steph_end = m.eval(meet_stephanie_end).as_long()
        john_start_time = m.eval(meet_john_start).as_long()
        john_end_time = m.eval(meet_john_end).as_long()

        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            hours = (minutes) // 60
            mins = (minutes) % 60
            return f"{9 + hours}:{mins:02d}"

        print("Optimal Schedule:")
        print(f"Meet Stephanie from {minutes_to_time(steph_start)} to {minutes_to_time(steph_end)}")
        print(f"Meet John from {minutes_to_time(john_start_time)} to {minutes_to_time(john_end_time)}")
        print(f"Total time with friends: {total_time.as_long()} minutes")
    else:
        print("No valid schedule found.")

solve_scheduling()