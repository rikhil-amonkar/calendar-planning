from z3 import *

def solve_scheduling():
    s = Solver()

    # Locations and indices
    locations = {
        "Golden Gate Park": 0,
        "Haight-Ashbury": 1,
        "Fisherman's Wharf": 2,
        "The Castro": 3,
        "Chinatown": 4,
        "Alamo Square": 5,
        "North Beach": 6,
        "Russian Hill": 7
    }

    # Travel times matrix (minutes)
    travel = [
        [0, 7, 24, 13, 23, 10, 24, 19],
        [7, 0, 23, 6, 19, 5, 19, 17],
        [25, 22, 0, 26, 12, 20, 6, 7],
        [11, 6, 24, 0, 20, 8, 20, 18],
        [23, 19, 8, 22, 0, 17, 3, 7],
        [9, 5, 19, 8, 16, 0, 15, 13],
        [22, 18, 5, 22, 6, 16, 0, 4],
        [21, 17, 7, 21, 9, 15, 5, 0]
    ]

    # Friends data: name, location, start, end, duration (minutes)
    friends = [
        ("Carol", "Haight-Ashbury", 21*60+30, 22*60+30, 60),
        ("Laura", "Fisherman's Wharf", 11*60+45, 21*60+30, 60),
        ("Karen", "The Castro", 7*60+15, 14*60+0, 75),
        ("Elizabeth", "Chinatown", 12*60+15, 21*60+30, 75),
        ("Deborah", "Alamo Square", 12*60+0, 15*60+0, 105),
        ("Jason", "North Beach", 14*60+45, 19*60+0, 90),
        ("Steven", "Russian Hill", 14*60+45, 18*60+30, 120)
    ]

    # Variables for arrival and departure times
    arrival = [Int(f"arr_{loc}") for loc in locations]
    departure = [Int(f"dep_{loc}") for loc in locations]

    # Visit order variables
    visit_order = [Int(f"visit_{i}") for i in range(7)]  # 7 locations to visit

    # Initial constraints
    s.add(arrival[locations["Golden Gate Park"]] == 0)
    s.add(departure[locations["Golden Gate Park"]] >= 0)

    # All locations must be visited exactly once (except start)
    s.add(Distinct(visit_order))
    for i in range(7):
        s.add(And(visit_order[i] >= 1, visit_order[i] <= 7))

    # Meeting constraints for each friend
    for name, loc, start, end, dur in friends:
        loc_idx = locations[loc]
        s.add(arrival[loc_idx] >= start - 9*60)
        s.add(departure[loc_idx] <= end - 9*60)
        s.add(departure[loc_idx] - arrival[loc_idx] >= dur)

    # Travel time constraints between consecutive visits
    for i in range(6):  # 6 transitions between 7 visits
        current = visit_order[i]
        next_visit = visit_order[i+1]
        
        # Get location indices
        current_loc = If(current == 1, locations["Haight-Ashbury"],
                       If(current == 2, locations["Fisherman's Wharf"],
                       If(current == 3, locations["The Castro"],
                       If(current == 4, locations["Chinatown"],
                       If(current == 5, locations["Alamo Square"],
                       If(current == 6, locations["North Beach"],
                       locations["Russian Hill"]))))))
        
        next_loc = If(next_visit == 1, locations["Haight-Ashbury"],
                    If(next_visit == 2, locations["Fisherman's Wharf"],
                    If(next_visit == 3, locations["The Castro"],
                    If(next_visit == 4, locations["Chinatown"],
                    If(next_visit == 5, locations["Alamo Square"],
                    If(next_visit == 6, locations["North Beach"],
                    locations["Russian Hill"]))))))
        
        s.add(arrival[next_loc] >= departure[current_loc] + travel[current_loc][next_loc])

    # First visit must account for travel from Golden Gate Park
    first_visit = visit_order[0]
    first_loc = If(first_visit == 1, locations["Haight-Ashbury"],
                 If(first_visit == 2, locations["Fisherman's Wharf"],
                 If(first_visit == 3, locations["The Castro"],
                 If(first_visit == 4, locations["Chinatown"],
                 If(first_visit == 5, locations["Alamo Square"],
                 If(first_visit == 6, locations["North Beach"],
                 locations["Russian Hill"]))))))
    s.add(arrival[first_loc] >= travel[locations["Golden Gate Park"]][first_loc])

    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        # Print in visit order
        visit_sequence = sorted([(m.evaluate(visit_order[i]).as_long(), i) for i in range(7)])
        for order, i in visit_sequence:
            loc_idx = If(order == 1, locations["Haight-Ashbury"],
                       If(order == 2, locations["Fisherman's Wharf"],
                       If(order == 3, locations["The Castro"],
                       If(order == 4, locations["Chinatown"],
                       If(order == 5, locations["Alamo Square"],
                       If(order == 6, locations["North Beach"],
                       locations["Russian Hill"]))))))
            loc_name = [k for k,v in locations.items() if v == loc_idx][0]
            arr = m.evaluate(arrival[loc_idx]).as_long()
            dep = m.evaluate(departure[loc_idx]).as_long()
            print(f"Visit {order}: Meet at {loc_name} from {9 + arr//60}:{arr%60:02d} to {9 + dep//60}:{dep%60:02d}")
    else:
        print("No valid schedule found")

solve_scheduling()