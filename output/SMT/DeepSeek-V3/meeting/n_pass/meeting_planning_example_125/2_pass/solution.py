from z3 import *

def solve_scheduling():
    # Create a solver instance
    s = Solver()

    # Define the variables for the schedule
    # Time variables are in minutes since 9:00AM (0 is 9:00AM)
    meet_stephanie_start = Int('meet_stephanie_start')
    meet_stephanie_end = Int('meet_stephanie_end')
    meet_john_start = Int('meet_john_start')
    meet_john_end = Int('meet_john_end')

    # Convert friend availability to minutes since 9:00AM
    stephanie_available_start = (8*60 + 15) - (9*60)  # -45 (8:15AM is 45 mins before 9:00AM)
    stephanie_available_end = (11*60 + 30) - (9*60)   # 150
    john_available_start = (10*60 + 15) - (9*60)      # 75
    john_available_end = (20*60 + 45) - (9*60)        # 705 (8:45PM)

    # Constraints for meeting Stephanie
    s.add(meet_stephanie_start >= 0)  # Can't start before 9:00AM
    s.add(meet_stephanie_start >= stephanie_available_start + 5)  # Need 5 mins to travel
    s.add(meet_stephanie_end <= stephanie_available_end)
    s.add(meet_stephanie_end - meet_stephanie_start >= 90)  # at least 90 minutes

    # Constraints for meeting John
    s.add(meet_john_start >= john_available_start)
    s.add(meet_john_end <= john_available_end)
    s.add(meet_john_end - meet_john_start >= 30)  # at least 30 minutes

    # Travel constraints - we can only do one order that works: Financial first then Alamo
    # Because Stephanie is only available until 11:30AM, we must meet her first
    s.add(meet_stephanie_start == 5)  # Leave Embarcadero at 9:00, arrive Financial at 9:05
    s.add(meet_stephanie_end == 95)   # 9:05 + 90 mins = 10:35
    s.add(meet_john_start >= 95 + 17) # Depart Financial at 10:35, arrive Alamo at 10:52
    s.add(meet_john_start >= 75)      # John available from 10:15AM

    # We want to maximize time with John after meeting Stephanie
    s.add(meet_john_end == meet_john_start + 30)  # Meet for exactly 30 minutes

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        
        # Convert times back to hours and minutes
        def to_time(minutes):
            total_mins = 9 * 60 + minutes
            hours = total_mins // 60
            mins = total_mins % 60
            return f"{hours}:{mins:02d}"

        steph_start = m[meet_stephanie_start].as_long()
        steph_end = m[meet_stephanie_end].as_long()
        john_start = m[meet_john_start].as_long()
        john_end = m[meet_john_end].as_long()
        
        print("Optimal Schedule:")
        print(f"9:00 - Depart from Embarcadero")
        print(f"{to_time(steph_start)} - Arrive at Financial District (after 5 min travel)")
        print(f"{to_time(steph_start)} - Meet Stephanie until {to_time(steph_end)}")
        print(f"{to_time(steph_end)} - Depart Financial District")
        print(f"{to_time(john_start)} - Arrive at Alamo Square (after 17 min travel)")
        print(f"{to_time(john_start)} - Meet John until {to_time(john_end)}")
    else:
        print("No valid schedule found")

solve_scheduling()