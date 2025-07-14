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
    leave_embarcadero = Int('leave_embarcadero')
    leave_financial = Int('leave_financial')
    leave_alamo = Int('leave_alamo')

    # Convert friend availability to minutes since 9:00AM
    stephanie_available_start = (8*60 + 15) - (9*60)  # -45 (8:15AM is 45 mins before 9:00AM)
    stephanie_available_end = (11*60 + 30) - (9*60)   # 150
    john_available_start = (10*60 + 15) - (9*60)      # 75
    john_available_end = (20*60 + 45) - (9*60)        # 705 (8:45PM)

    # Constraints for meeting Stephanie
    s.add(meet_stephanie_start >= stephanie_available_start)
    s.add(meet_stephanie_end <= stephanie_available_end)
    s.add(meet_stephanie_end - meet_stephanie_start >= 90)  # at least 90 minutes
    s.add(meet_stephanie_start >= 0)  # can't start before 9:00AM

    # Constraints for meeting John
    s.add(meet_john_start >= john_available_start)
    s.add(meet_john_end <= john_available_end)
    s.add(meet_john_end - meet_john_start >= 30)  # at least 30 minutes

    # Travel constraints
    # Option 1: Embarcadero -> Financial -> Alamo
    # Option 2: Embarcadero -> Alamo -> Financial
    # We'll let Z3 choose the best order

    # Create a variable to represent the order
    order = Int('order')
    s.add(Or(order == 1, order == 2))  # 1: Financial first, 2: Alamo first

    # Constraints for order 1: Financial first
    s.add(Implies(order == 1,
                  And(leave_embarcadero == meet_stephanie_start - 5,  # travel to Financial takes 5 mins
                      meet_stephanie_end + 17 <= meet_john_start,     # travel to Alamo takes 17 mins
                      meet_john_end <= 720)))                         # end by 9:00PM (12 hours after start)

    # Constraints for order 2: Alamo first
    s.add(Implies(order == 2,
                  And(leave_embarcadero == meet_john_start - 19,      # travel to Alamo takes 19 mins
                      meet_john_end + 17 <= meet_stephanie_start,     # travel to Financial takes 17 mins
                      meet_stephanie_start >= 0,                      # can't start before 9:00AM
                      meet_stephanie_end <= 150)))                    # must finish by 11:30AM

    # We want to maximize the time with friends
    # Since meeting durations are fixed, we just need to find a feasible solution
    # Add a dummy optimization to prefer earlier schedules
    s.add(meet_stephanie_start >= 0)
    s.add(meet_john_start >= 0)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        order_val = m[order].as_long()
        
        # Convert times back to hours and minutes
        def to_time(minutes):
            total_mins = 9 * 60 + minutes
            hours = total_mins // 60
            mins = total_mins % 60
            return f"{hours}:{mins:02d}"

        if order_val == 1:
            # Financial first
            steph_start = m[meet_stephanie_start].as_long()
            steph_end = m[meet_stephanie_end].as_long()
            john_start = m[meet_john_start].as_long()
            john_end = m[meet_john_end].as_long()
            
            print("Optimal Schedule:")
            print(f"9:00 - Depart from Embarcadero")
            print(f"{to_time(steph_start - 5)} - Arrive at Financial District")
            print(f"{to_time(steph_start)} - Meet Stephanie until {to_time(steph_end)}")
            print(f"{to_time(steph_end)} - Depart Financial District")
            print(f"{to_time(steph_end + 17)} - Arrive at Alamo Square")
            print(f"{to_time(john_start)} - Meet John until {to_time(john_end)}")
        else:
            # Alamo first
            john_start = m[meet_john_start].as_long()
            john_end = m[meet_john_end].as_long()
            steph_start = m[meet_stephanie_start].as_long()
            steph_end = m[meet_stephanie_end].as_long()
            
            print("Optimal Schedule:")
            print(f"9:00 - Depart from Embarcadero")
            print(f"{to_time(john_start - 19)} - Arrive at Alamo Square")
            print(f"{to_time(john_start)} - Meet John until {to_time(john_end)}")
            print(f"{to_time(john_end)} - Depart Alamo Square")
            print(f"{to_time(john_end + 17)} - Arrive at Financial District")
            print(f"{to_time(steph_start)} - Meet Stephanie until {to_time(steph_end)}")
    else:
        print("No valid schedule found")

solve_scheduling()