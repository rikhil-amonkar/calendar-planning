from z3 import *

def main():
    # Travel time dictionary
    travel_dict = {
        ('start', 'north'): 29,
        ('start', 'union'): 30,
        ('start', 'alamo'): 17,
        ('north', 'start'): 27,
        ('north', 'union'): 7,
        ('north', 'alamo'): 16,
        ('union', 'start'): 26,
        ('union', 'north'): 10,
        ('union', 'alamo'): 15,
        ('alamo', 'start'): 16,
        ('alamo', 'north'): 15,
        ('alamo', 'union'): 14,
    }

    # Friend data: (name, location, availability start, availability end, duration)
    # Times in minutes from 9:00 AM
    friends_data = [
        ('s', 'north', 7*60, 9*60 + 15, 60),  # Sarah: 4:00 PM to 6:15 PM, 60 min
        ('j', 'union', 6*60, 13*60, 75),       # Jeffrey: 3:00 PM to 10:00 PM, 75 min
        ('b', 'alamo', 7*60, 8*60 + 30, 75)    # Brian: 4:00 PM to 5:30 PM, 75 min (must start by 4:15 PM)
    ]

    s_met, j_met, b_met = Bools('s_met j_met b_met')
    s_start, j_start, b_start = Ints('s_start j_start b_start')
    s_order, j_order, b_order = Ints('s_order j_order b_order')

    # Friend variables for easy iteration
    friends = [
        ('s', s_met, s_start, s_order, 'north', friends_data[0][2], friends_data[0][3], friends_data[0][4]),
        ('j', j_met, j_start, j_order, 'union', friends_data[1][2], friends_data[1][3], friends_data[1][4]),
        ('b', b_met, b_start, b_order, 'alamo', friends_data[2][2], friends_data[2][3], friends_data[2][4])
    ]

    solver = Optimize()
    constraints = []

    # Individual meeting constraints
    for name, met, start, order, loc, avail_low, avail_high, dur in friends:
        constraints.append(If(met, 
                             And(start >= avail_low, 
                                 start <= avail_high - dur, 
                                 start >= travel_dict[('start', loc)]), 
                             True))
        constraints.append(If(met, order >= 1, order == 0))

    # Order constraints for every pair of friends
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            name_i, met_i, start_i, order_i, loc_i, avail_low_i, avail_high_i, dur_i = friends[i]
            name_j, met_j, start_j, order_j, loc_j, avail_low_j, avail_high_j, dur_j = friends[j]
            # If both meetings happen, they must have distinct orders
            constraints.append(If(And(met_i, met_j), order_i != order_j, True))
            # Travel time constraints based on order
            both_met = And(met_i, met_j)
            if loc_i == loc_j:
                # Same location, no travel time but cannot overlap
                constraints.append(If(both_met, 
                                     Or(start_i + dur_i <= start_j, 
                                        start_j + dur_j <= start_i), 
                                     True))
            else:
                # Different locations: travel time required
                constraints.append(If(both_met, 
                                     If(order_i < order_j, 
                                        start_i + dur_i + travel_dict[(loc_i, loc_j)] <= start_j,
                                        start_j + dur_j + travel_dict[(loc_j, loc_i)] <= start_i), 
                                     True))

    # Add all constraints
    solver.add(constraints)

    # Maximize the number of friends met
    num_met = If(s_met, 1, 0) + If(j_met, 1, 0) + If(b_met, 1, 0)
    solver.maximize(num_met)

    # Check and get the solution
    if solver.check() == sat:
        model = solver.model()
        print("SOLUTION:")
        # Convert minutes to time string
        def min_to_time(m):
            h = 9 + m // 60
            m_min = m % 60
            if h < 12:
                return f"{h}:{m_min:02d} AM"
            elif h == 12:
                return f"12:{m_min:02d} PM"
            else:
                return f"{h-12}:{m_min:02d} PM"
        
        for name, met, start, order, loc, avail_low, avail_high, dur in friends:
            if is_true(model[met]):
                start_val = model[start].as_long()
                end_val = start_val + dur
                print(f"Meet {'Sarah' if name == 's' else 'Jeffrey' if name == 'j' else 'Brian'} "
                      f"at {loc} from {min_to_time(start_val)} to {min_to_time(end_val)}")
        print(f"Total friends met: {model.evaluate(num_met)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()