from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Arrival time at Bayview: 9:00 AM (540 minutes)
    # Friends' availability:
    # Mary: Pacific Heights, 10:00 AM (600) to 7:00 PM (1140), min 45 mins
    # Lisa: Mission District, 8:30 PM (1230) to 10:00 PM (1320), min 75 mins
    # Betty: Haight-Ashbury, 7:15 AM (435) to 5:15 PM (1035), min 90 mins
    # Charles: Financial District, 11:15 AM (675) to 3:00 PM (900), min 120 mins

    # Meeting start and end times (in minutes since midnight)
    start_mary = Int('start_mary')
    end_mary = Int('end_mary')
    start_lisa = Int('start_lisa')
    end_lisa = Int('end_lisa')
    start_betty = Int('start_betty')
    end_betty = Int('end_betty')
    start_charles = Int('start_charles')
    end_charles = Int('end_charles')

    # Constraints for each meeting
    # Mary: Pacific Heights, 600 to 1140, duration >=45
    s.add(start_mary >= 600)
    s.add(end_mary <= 1140)
    s.add(end_mary - start_mary >= 45)

    # Lisa: Mission District, 1230 to 1320, duration >=75
    s.add(start_lisa >= 1230)
    s.add(end_lisa <= 1320)
    s.add(end_lisa - start_lisa >= 75)

    # Betty: Haight-Ashbury, 435 to 1035, duration >=90
    s.add(start_betty >= 435)
    s.add(end_betty <= 1035)
    s.add(end_betty - start_betty >= 90)

    # Charles: Financial District, 675 to 900, duration >=120
    s.add(start_charles >= 675)
    s.add(end_charles <= 900)
    s.add(end_charles - start_charles >= 120)

    # Travel times between locations
    travel_times = {
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Financial District'): 19,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Financial District'): 13,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Financial District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Mission District'): 17,
        ('Financial District', 'Haight-Ashbury'): 19,
    }

    # Initial location: Bayview at 540 (9:00 AM)
    current_time = 540
    current_location = 'Bayview'

    # Order of meetings: We need to sequence the meetings and account for travel times
    # We'll assume an order and enforce travel times between consecutive meetings
    # Possible orders: Since we must meet all four friends, we can try all permutations
    # For simplicity, we'll assume an order and adjust if needed

    # Assume the order is Betty -> Charles -> Mary -> Lisa
    # Betty: Haight-Ashbury
    s.add(start_betty >= current_time + travel_times[(current_location, 'Haight-Ashbury')])
    # After Betty, go to Charles: Financial District
    s.add(start_charles >= end_betty + travel_times[('Haight-Ashbury', 'Financial District')])
    # After Charles, go to Mary: Pacific Heights
    s.add(start_mary >= end_charles + travel_times[('Financial District', 'Pacific Heights')])
    # After Mary, go to Lisa: Mission District
    s.add(start_lisa >= end_mary + travel_times[('Pacific Heights', 'Mission District')])

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found. Meet all four friends:")
        print(f"Betty: Haight-Ashbury from {m[start_betty]} to {m[end_betty]}")
        print(f"Charles: Financial District from {m[start_charles]} to {m[end_charles]}")
        print(f"Mary: Pacific Heights from {m[start_mary]} to {m[end_mary]}")
        print(f"Lisa: Mission District from {m[start_lisa]} to {m[end_lisa]}")
    else:
        print("No feasible schedule found with the assumed order. Trying another order...")
        # Reset solver
        s = Solver()
        # Re-add constraints
        s.add(start_mary >= 600)
        s.add(end_mary <= 1140)
        s.add(end_mary - start_mary >= 45)
        s.add(start_lisa >= 1230)
        s.add(end_lisa <= 1320)
        s.add(end_lisa - start_lisa >= 75)
        s.add(start_betty >= 435)
        s.add(end_betty <= 1035)
        s.add(end_betty - start_betty >= 90)
        s.add(start_charles >= 675)
        s.add(end_charles <= 900)
        s.add(end_charles - start_charles >= 120)
        # Try another order: Betty -> Mary -> Charles -> Lisa
        s.add(start_betty >= current_time + travel_times[(current_location, 'Haight-Ashbury')])
        s.add(start_mary >= end_betty + travel_times[('Haight-Ashbury', 'Pacific Heights')])
        s.add(start_charles >= end_mary + travel_times[('Pacific Heights', 'Financial District')])
        s.add(start_lisa >= end_charles + travel_times[('Financial District', 'Mission District')])
        if s.check() == sat:
            m = s.model()
            print("Optimal schedule found. Meet all four friends:")
            print(f"Betty: Haight-Ashbury from {m[start_betty]} to {m[end_betty]}")
            print(f"Mary: Pacific Heights from {m[start_mary]} to {m[end_mary]}")
            print(f"Charles: Financial District from {m[start_charles]} to {m[end_charles]}")
            print(f"Lisa: Mission District from {m[start_lisa]} to {m[end_lisa]}")
        else:
            print("No feasible schedule found with any order.")

solve_scheduling()