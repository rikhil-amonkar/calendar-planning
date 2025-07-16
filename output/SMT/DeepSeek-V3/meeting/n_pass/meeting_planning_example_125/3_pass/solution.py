from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Variables (in minutes since 9:00 AM)
    meet_stephanie_start = Int('meet_stephanie_start')
    meet_stephanie_end = Int('meet_stephanie_end')
    meet_john_start = Int('meet_john_start')
    meet_john_end = Int('meet_john_end')

    # Travel times (minutes)
    emb_to_fin = 5      # Embarcadero to Financial District
    fin_to_alamo = 17   # Financial District to Alamo Square
    emb_to_alamo = 19   # Embarcadero to Alamo Square
    alamo_to_emb = 17   # Alamo Square to Embarcadero

    # Availability windows (minutes since 9:00 AM)
    # Stephanie: 8:15-11:30 AM → -45 to 150 minutes
    # John: 10:15 AM-8:45 PM → 75 to 705 minutes

    # Constraints for Stephanie
    s.add(meet_stephanie_start >= 0)  # Can't start before 9:00 AM
    s.add(meet_stephanie_end <= 150)  # Must end by 11:30 AM
    s.add(meet_stephanie_end - meet_stephanie_start >= 90)  # Min 90 minutes

    # Constraints for John
    s.add(meet_john_start >= 75)      # Can't start before 10:15 AM
    s.add(meet_john_end <= 705)       # Must end by 8:45 PM
    s.add(meet_john_end - meet_john_start >= 30)  # Min 30 minutes

    # Define meeting order options
    # Option 1: Meet Stephanie first, then John
    option1 = And(
        meet_stephanie_start >= emb_to_fin,  # Travel to Financial District
        meet_john_start >= meet_stephanie_end + fin_to_alamo  # Travel to Alamo Square
    )

    # Option 2: Meet John first, then Stephanie
    option2 = And(
        meet_john_start >= emb_to_alamo,  # Travel to Alamo Square
        meet_stephanie_start >= meet_john_end + fin_to_alamo  # Travel to Financial District
    )

    # Only one option can be true
    s.add(Or(option1, option2))

    # Maximize total meeting time
    total_time = (meet_stephanie_end - meet_stephanie_start) + (meet_john_end - meet_john_start)
    s.maximize(total_time)

    # Check for solution
    if s.check() == sat:
        m = s.model()
        steph_start = m.eval(meet_stephanie_start).as_long()
        steph_end = m.eval(meet_stephanie_end).as_long()
        john_start = m.eval(meet_john_start).as_long()
        john_end = m.eval(meet_john_end).as_long()

        # Convert minutes to time strings
        def format_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            ampm = "AM" if hours < 12 else "PM"
            hours = hours if hours <= 12 else hours - 12
            return f"{hours}:{mins:02d} {ampm}"

        print("\nOptimal Schedule Found:")
        print(f"• Meet Stephanie: {format_time(steph_start)} to {format_time(steph_end)}")
        print(f"• Meet John: {format_time(john_start)} to {format_time(john_end)}")
        print(f"\nTotal meeting time: {total_time.as_long()} minutes")
        
        # Calculate travel details
        if m.eval(option1):
            print("\nTravel Plan:")
            print(f"1. 9:00 AM: Start at Embarcadero")
            print(f"2. 9:05 AM: Arrive at Financial District (travel time: 5 min)")
            print(f"3. {format_time(steph_end)}: Leave Financial District")
            print(f"4. {format_time(steph_end + fin_to_alamo)}: Arrive at Alamo Square (travel time: 17 min)")
        else:
            print("\nTravel Plan:")
            print(f"1. 9:00 AM: Start at Embarcadero")
            print(f"2. 9:19 AM: Arrive at Alamo Square (travel time: 19 min)")
            print(f"3. {format_time(john_end)}: Leave Alamo Square")
            print(f"4. {format_time(john_end + fin_to_alamo)}: Arrive at Financial District (travel time: 17 min)")
    else:
        print("No valid schedule found that meets all constraints.")

solve_scheduling()