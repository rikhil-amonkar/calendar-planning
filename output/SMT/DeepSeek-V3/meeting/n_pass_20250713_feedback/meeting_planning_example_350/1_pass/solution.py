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

    # Decision variables: whether to meet each friend (1 if met, 0 otherwise)
    meet_mary = Int('meet_mary')
    meet_lisa = Int('meet_lisa')
    meet_betty = Int('meet_betty')
    meet_charles = Int('meet_charles')

    # Each meet variable is 0 or 1
    s.add(Or(meet_mary == 0, meet_mary == 1))
    s.add(Or(meet_lisa == 0, meet_lisa == 1))
    s.add(Or(meet_betty == 0, meet_betty == 1))
    s.add(Or(meet_charles == 0, meet_charles == 1))

    # Meeting start and end times (in minutes since midnight)
    start_mary = Int('start_mary')
    end_mary = Int('end_mary')
    start_lisa = Int('start_lisa')
    end_lisa = Int('end_lisa')
    start_betty = Int('start_betty')
    end_betty = Int('end_betty')
    start_charles = Int('start_charles')
    end_charles = Int('end_charles')

    # Constraints for each meeting if it happens
    # Mary: Pacific Heights, 600 to 1140, duration >=45
    s.add(Implies(meet_mary == 1, And(start_mary >= 600, end_mary <= 1140, end_mary - start_mary >= 45)))
    s.add(Implies(meet_mary == 0, And(start_mary == 0, end_mary == 0)))

    # Lisa: Mission District, 1230 to 1320, duration >=75
    s.add(Implies(meet_lisa == 1, And(start_lisa >= 1230, end_lisa <= 1320, end_lisa - start_lisa >= 75)))
    s.add(Implies(meet_lisa == 0, And(start_lisa == 0, end_lisa == 0)))

    # Betty: Haight-Ashbury, 435 to 1035, duration >=90
    s.add(Implies(meet_betty == 1, And(start_betty >= 435, end_betty <= 1035, end_betty - start_betty >= 90)))
    s.add(Implies(meet_betty == 0, And(start_betty == 0, end_betty == 0)))

    # Charles: Financial District, 675 to 900, duration >=120
    s.add(Implies(meet_charles == 1, And(start_charles >= 675, end_charles <= 900, end_charles - start_charles >= 120)))
    s.add(Implies(meet_charles == 0, And(start_charles == 0, end_charles == 0)))

    # Initial location: Bayview at 540 (9:00 AM)
    current_time = 540
    current_location = 'Bayview'

    # Define the order of meetings and travel times
    # We need to sequence the meetings and account for travel times between them.
    # To model this, we'll create variables for the order and ensure travel times are respected.

    # We'll use a list to represent the possible meetings and their locations.
    meetings = [
        ('mary', 'Pacific Heights', meet_mary, start_mary, end_mary),
        ('lisa', 'Mission District', meet_lisa, start_lisa, end_lisa),
        ('betty', 'Haight-Ashbury', meet_betty, start_betty, end_betty),
        ('charles', 'Financial District', meet_charles, start_charles, end_charles)
    ]

    # We need to sequence the meetings. For simplicity, we'll assume that the meetings are done in some order.
    # However, modeling all possible permutations is complex. Instead, we'll use auxiliary variables to represent the order.

    # For each meeting that is selected (meet_X == 1), its start time must be >= current_time + travel time from current_location to meeting location.
    # We'll need to track the current_location and current_time after each meeting.

    # This is complex to model in Z3 directly. Instead, we'll use a more straightforward approach by considering possible sequences.

    # Alternative approach: since the number of friends is small (4), we can model all possible permutations of the selected meetings.

    # However, given the complexity, we'll proceed with a simplified model where we ensure that for any two meetings, if both are selected, one must start after the other plus travel time.

    # For each pair of distinct meetings, if both are selected, then one must start after the other's end plus travel time.
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

    # For each pair of meetings, if both are selected, then one must be scheduled after the other with travel time.
    # We'll create a binary variable for the order of each pair.
    # This is a more scalable approach.

    # Create order variables for each pair of meetings
    order_mary_betty = Int('order_mary_betty')
    order_mary_charles = Int('order_mary_charles')
    order_mary_lisa = Int('order_mary_lisa')
    order_betty_charles = Int('order_betty_charles')
    order_betty_lisa = Int('order_betty_lisa')
    order_charles_lisa = Int('order_charles_lisa')

    # Each order variable is 0 or 1 (0: first before second, 1: second before first)
    s.add(Or(order_mary_betty == 0, order_mary_betty == 1))
    s.add(Or(order_mary_charles == 0, order_mary_charles == 1))
    s.add(Or(order_mary_lisa == 0, order_mary_lisa == 1))
    s.add(Or(order_betty_charles == 0, order_betty_charles == 1))
    s.add(Or(order_betty_lisa == 0, order_betty_lisa == 1))
    s.add(Or(order_charles_lisa == 0, order_charles_lisa == 1))

    # Constraints for each pair
    # Mary and Betty
    s.add(Implies(And(meet_mary == 1, meet_betty == 1), 
          Or(
              And(order_mary_betty == 0, 
                  start_betty >= end_mary + travel_times[('Pacific Heights', 'Haight-Ashbury')]),
              And(order_mary_betty == 1, 
                  start_mary >= end_betty + travel_times[('Haight-Ashbury', 'Pacific Heights')])
          ))

    # Mary and Charles
    s.add(Implies(And(meet_mary == 1, meet_charles == 1), 
          Or(
              And(order_mary_charles == 0, 
                  start_charles >= end_mary + travel_times[('Pacific Heights', 'Financial District')]),
              And(order_mary_charles == 1, 
                  start_mary >= end_charles + travel_times[('Financial District', 'Pacific Heights')])
          ))

    # Mary and Lisa
    s.add(Implies(And(meet_mary == 1, meet_lisa == 1), 
          Or(
              And(order_mary_lisa == 0, 
                  start_lisa >= end_mary + travel_times[('Pacific Heights', 'Mission District')]),
              And(order_mary_lisa == 1, 
                  start_mary >= end_lisa + travel_times[('Mission District', 'Pacific Heights')])
          ))

    # Betty and Charles
    s.add(Implies(And(meet_betty == 1, meet_charles == 1), 
          Or(
              And(order_betty_charles == 0, 
                  start_charles >= end_betty + travel_times[('Haight-Ashbury', 'Financial District')]),
              And(order_betty_charles == 1, 
                  start_betty >= end_charles + travel_times[('Financial District', 'Haight-Ashbury')])
          ))

    # Betty and Lisa
    s.add(Implies(And(meet_betty == 1, meet_lisa == 1), 
          Or(
              And(order_betty_lisa == 0, 
                  start_lisa >= end_betty + travel_times[('Haight-Ashbury', 'Mission District')]),
              And(order_betty_lisa == 1, 
                  start_betty >= end_lisa + travel_times[('Mission District', 'Haight-Ashbury')])
          ))

    # Charles and Lisa
    s.add(Implies(And(meet_charles == 1, meet_lisa == 1), 
          Or(
              And(order_charles_lisa == 0, 
                  start_lisa >= end_charles + travel_times[('Financial District', 'Mission District')]),
              And(order_charles_lisa == 1, 
                  start_charles >= end_lisa + travel_times[('Mission District', 'Financial District')])
          ))

    # Also, the first meeting must start after current_time (540) + travel time from Bayview to the meeting's location.
    s.add(Implies(meet_mary == 1, start_mary >= 540 + travel_times[('Bayview', 'Pacific Heights')]))
    s.add(Implies(meet_betty == 1, start_betty >= 540 + travel_times[('Bayview', 'Haight-Ashbury')]))
    s.add(Implies(meet_charles == 1, start_charles >= 540 + travel_times[('Bayview', 'Financial District')]))
    s.add(Implies(meet_lisa == 1, start_lisa >= 540 + travel_times[('Bayview', 'Mission District')]))

    # Objective: maximize the number of friends met
    total_met = meet_mary + meet_betty + meet_charles + meet_lisa
    s.maximize(total_met)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found. Meet the following friends:")
        if m[meet_mary].as_long() == 1:
            print(f"Mary: Pacific Heights from {m[start_mary]} to {m[end_mary]}")
        if m[meet_betty].as_long() == 1:
            print(f"Betty: Haight-Ashbury from {m[start_betty]} to {m[end_betty]}")
        if m[meet_charles].as_long() == 1:
            print(f"Charles: Financial District from {m[start_charles]} to {m[end_charles]}")
        if m[meet_lisa].as_long() == 1:
            print(f"Lisa: Mission District from {m[start_lisa]} to {m[end_lisa]}")
        print(f"Total friends met: {m[total_met]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()