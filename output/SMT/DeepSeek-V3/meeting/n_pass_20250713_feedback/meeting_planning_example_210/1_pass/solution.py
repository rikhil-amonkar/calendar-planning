from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Arrival time at Fisherman's Wharf: 9:00 AM (540 minutes)
    arrival_time = 540

    # Friends' availability windows (in minutes since midnight)
    emily_start = 16 * 60 + 15  # 4:15 PM (975 minutes)
    emily_end = 21 * 60         # 9:00 PM (1260 minutes)
    joseph_start = 17 * 60 + 15 # 5:15 PM (1035 minutes)
    joseph_end = 22 * 60        # 10:00 PM (1320 minutes)
    melissa_start = 15 * 60 + 45 # 3:45 PM (945 minutes)
    melissa_end = 21 * 60 + 45   # 9:45 PM (1305 minutes)

    # Meeting durations (in minutes)
    emily_duration = 105
    joseph_duration = 120
    melissa_duration = 75

    # Travel times (in minutes)
    travel = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
    }

    # Variables for meeting start and end times
    emily_meet_start = Int('emily_meet_start')
    emily_meet_end = Int('emily_meet_end')
    joseph_meet_start = Int('joseph_meet_start')
    joseph_meet_end = Int('joseph_meet_end')
    melissa_meet_start = Int('melissa_meet_start')
    melissa_meet_end = Int('melissa_meet_end')

    # Constraints for meeting durations
    s.add(emily_meet_end == emily_meet_start + emily_duration)
    s.add(joseph_meet_end == joseph_meet_start + joseph_duration)
    s.add(melissa_meet_end == melissa_meet_start + melissa_duration)

    # Constraints for meeting within friends' availability
    s.add(emily_meet_start >= emily_start)
    s.add(emily_meet_end <= emily_end)
    s.add(joseph_meet_start >= joseph_start)
    s.add(joseph_meet_end <= joseph_end)
    s.add(melissa_meet_start >= melissa_start)
    s.add(melissa_meet_end <= melissa_end)

    # Variables to track the order of meetings and travel times
    # We need to decide the order of meetings. There are 3! = 6 possible orders.
    # We'll encode the order as a permutation of [melissa, emily, joseph].

    # To handle the order, we'll use auxiliary variables to represent the sequence.
    # For simplicity, we'll assume a fixed order and let Z3 find the correct one.
    # Alternatively, we can encode all possible orders and let Z3 choose.

    # Let's assume the order is Melissa -> Emily -> Joseph.
    # Then, we need to account for travel times between them.

    # Start at Fisherman's Wharf at 540 minutes (9:00 AM).
    # First, go to Financial District to meet Melissa.
    travel_to_melissa = travel[('Fisherman\'s Wharf', 'Financial District')]
    s.add(melissa_meet_start >= arrival_time + travel_to_melissa)

    # After Melissa, go to Presidio to meet Emily.
    travel_melissa_to_emily = travel[('Financial District', 'Presidio')]
    s.add(emily_meet_start >= melissa_meet_end + travel_melissa_to_emily)

    # After Emily, go to Richmond District to meet Joseph.
    travel_emily_to_joseph = travel[('Presidio', 'Richmond District')]
    s.add(joseph_meet_start >= emily_meet_end + travel_emily_to_joseph)

    # Check if this order is feasible. If not, try another order.
    # We'll use a more general approach by allowing Z3 to choose the order.

    # Alternative approach: Introduce variables to represent the order.
    # This is more complex but more general.

    # For simplicity, we'll proceed with the fixed order and check if it works.
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Melissa at Financial District from {m[melissa_meet_start]} to {m[melissa_meet_end]} minutes.")
        print(f"Then meet Emily at Presidio from {m[emily_meet_start]} to {m[emily_meet_end]} minutes.")
        print(f"Then meet Joseph at Richmond District from {m[joseph_meet_start]} to {m[joseph_meet_end]} minutes.")
    else:
        # Try another order: Melissa -> Joseph -> Emily
        s.reset()
        s.add(emily_meet_end == emily_meet_start + emily_duration)
        s.add(joseph_meet_end == joseph_meet_start + joseph_duration)
        s.add(melissa_meet_end == melissa_meet_start + melissa_duration)
        s.add(emily_meet_start >= emily_start)
        s.add(emily_meet_end <= emily_end)
        s.add(joseph_meet_start >= joseph_start)
        s.add(joseph_meet_end <= joseph_end)
        s.add(melissa_meet_start >= melissa_start)
        s.add(melissa_meet_end <= melissa_end)

        travel_to_melissa = travel[('Fisherman\'s Wharf', 'Financial District')]
        s.add(melissa_meet_start >= arrival_time + travel_to_melissa)

        travel_melissa_to_joseph = travel[('Financial District', 'Richmond District')]
        s.add(joseph_meet_start >= melissa_meet_end + travel_melissa_to_joseph)

        travel_joseph_to_emily = travel[('Richmond District', 'Presidio')]
        s.add(emily_meet_start >= joseph_meet_end + travel_joseph_to_emily)

        if s.check() == sat:
            m = s.model()
            print("SOLUTION:")
            print(f"Meet Melissa at Financial District from {m[melissa_meet_start]} to {m[melissa_meet_end]} minutes.")
            print(f"Then meet Joseph at Richmond District from {m[joseph_meet_start]} to {m[joseph_meet_end]} minutes.")
            print(f"Then meet Emily at Presidio from {m[emily_meet_start]} to {m[emily_meet_end]} minutes.")
        else:
            # Try another order: Emily -> Melissa -> Joseph
            s.reset()
            s.add(emily_meet_end == emily_meet_start + emily_duration)
            s.add(joseph_meet_end == joseph_meet_start + joseph_duration)
            s.add(melissa_meet_end == melissa_meet_start + melissa_duration)
            s.add(emily_meet_start >= emily_start)
            s.add(emily_meet_end <= emily_end)
            s.add(joseph_meet_start >= joseph_start)
            s.add(joseph_meet_end <= joseph_end)
            s.add(melissa_meet_start >= melissa_start)
            s.add(melissa_meet_end <= melissa_end)

            travel_to_emily = travel[('Fisherman\'s Wharf', 'Presidio')]
            s.add(emily_meet_start >= arrival_time + travel_to_emily)

            travel_emily_to_melissa = travel[('Presidio', 'Financial District')]
            s.add(melissa_meet_start >= emily_meet_end + travel_emily_to_melissa)

            travel_melissa_to_joseph = travel[('Financial District', 'Richmond District')]
            s.add(joseph_meet_start >= melissa_meet_end + travel_melissa_to_joseph)

            if s.check() == sat:
                m = s.model()
                print("SOLUTION:")
                print(f"Meet Emily at Presidio from {m[emily_meet_start]} to {m[emily_meet_end]} minutes.")
                print(f"Then meet Melissa at Financial District from {m[melissa_meet_start]} to {m[melissa_meet_end]} minutes.")
                print(f"Then meet Joseph at Richmond District from {m[joseph_meet_start]} to {m[joseph_meet_end]} minutes.")
            else:
                print("No feasible schedule found.")

solve_scheduling()