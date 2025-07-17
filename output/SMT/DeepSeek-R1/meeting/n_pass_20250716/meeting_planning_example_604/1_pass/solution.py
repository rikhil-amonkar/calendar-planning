from z3 import *

def main():
    # Define locations and travel time matrix
    # 0: Fisherman's Wharf, 1: The Castro, 2: Golden Gate Park, 3: Russian Hill, 4: Alamo Square, 5: North Beach
    n_locations = 6
    travel_time = [
        [0, 26, 25, 7, 20, 6],
        [24, 0, 11, 18, 8, 20],
        [24, 13, 0, 19, 10, 24],
        [7, 21, 21, 0, 15, 5],
        [19, 8, 9, 13, 0, 16],
        [5, 22, 22, 4, 16, 0]
    ]

    friends = [
        # (name, loc_index, min_dur, avail_start, avail_end)
        ("Laura", 1, 105, 645, 750),    # 0
        ("Daniel", 2, 15, 735, 765),     # 1
        ("Karen", 3, 30, 330, 645),      # 2
        ("Joseph", 4, 15, 150, 225),     # 3
        ("Kimberly", 5, 30, 405, 615)    # 4
    ]

    n_friends = len(friends)

    # Create solver
    opt = Optimize()

    # Create variables: meet and start for each friend
    meet = [Bool(f'meet_{i}') for i in range(n_friends)]
    start = [Int(f'start_{i}') for i in range(n_friends)]

    # Constraint 1: for each friend, if meet, then constraints on start time
    for i in range(n_friends):
        name, loc, dur, avail_s, avail_e = friends[i]
        opt.add(Implies(meet[i], start[i] >= avail_s))
        opt.add(Implies(meet[i], start[i] <= avail_e - dur))
        opt.add(Implies(meet[i], start[i] >= travel_time[0][loc]))

    # Constraint 2: pairwise disjunctive constraints for every pair of friends
    for i in range(n_friends):
        for j in range(i+1, n_friends):
            name_i, loc_i, dur_i, _, _ = friends[i]
            name_j, loc_j, dur_j, _, _ = friends[j]
            travel_ij = travel_time[loc_i][loc_j]
            travel_ji = travel_time[loc_j][loc_i]
            opt.add(Implies(And(meet[i], meet[j]),
                             Or( start[i] + dur_i + travel_ij <= start[j],
                                 start[j] + dur_j + travel_ji <= start[i] )))

    # Maximize the number of friends met
    opt.maximize(Sum([If(meet[i], 1, 0) for i in range(n_friends)]))

    # Check and get the model
    if opt.check() == sat:
        model = opt.model()
        total_met = 0
        schedule = []
        for i in range(n_friends):
            if model.eval(meet[i]):
                total_met += 1
                start_val = model.eval(start[i]).as_long()
                total_minutes = start_val
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                time_str = f"{hours}:{minutes:02d}"
                schedule.append((friends[i][0], time_str, total_minutes))
        print(f"Total friends met: {total_met}")
        schedule.sort(key=lambda x: x[2])
        for s in schedule:
            print(f"Meet {s[0]} at {s[1]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()