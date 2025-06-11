from z3 import *

def main():
    # Travel time matrix: 10 locations (0: Marina, 1: Embarcadero, 2: Bayview, 3: Union Square, 4: Chinatown, 
    # 5: Sunset District, 6: Golden Gate Park, 7: Financial District, 8: Haight-Ashbury, 9: Mission District)
    travel_time = [
        [0, 14, 27, 16, 15, 19, 18, 17, 16, 20],   # Marina (0)
        [12, 0, 21, 10, 7, 30, 25, 5, 21, 20],      # Embarcadero (1)
        [27, 19, 0, 18, 19, 23, 22, 19, 19, 13],    # Bayview (2)
        [18, 11, 15, 0, 7, 27, 22, 9, 18, 14],      # Union Square (3)
        [12, 5, 20, 7, 0, 29, 23, 5, 19, 17],       # Chinatown (4)
        [21, 30, 22, 30, 30, 0, 11, 30, 15, 25],    # Sunset District (5)
        [16, 25, 23, 22, 23, 10, 0, 26, 7, 17],     # Golden Gate Park (6)
        [15, 4, 19, 9, 5, 30, 23, 0, 19, 17],       # Financial District (7)
        [17, 20, 18, 19, 19, 15, 7, 21, 0, 11],     # Haight-Ashbury (8)
        [19, 19, 14, 15, 16, 24, 17, 15, 12, 0]     # Mission District (9)
    ]
    
    # Friend indices and their location indices (friend i is at location loc_index[i])
    # Joshua (0): Embarcadero -> 1
    # Jeffrey (1): Bayview -> 2
    # Charles (2): Union Square -> 3
    # Joseph (3): Chinatown -> 4
    # Elizabeth (4): Sunset District -> 5
    # Matthew (5): Golden Gate Park -> 6
    # Carol (6): Financial District -> 7
    # Paul (7): Haight-Ashbury -> 8
    # Rebecca (8): Mission District -> 9
    loc_index = [1, 2, 3, 4, 5, 6, 7, 8, 9]
    
    # Meeting durations in minutes
    durations = [105, 75, 120, 60, 45, 45, 15, 15, 45]
    
    # Time windows (start and end in minutes since 9:00 AM)
    window_start = [45, 45, 105, 0, 0, 120, 105, 615, 480]
    window_end = [540, 675, 675, 390, 45, 630, 135, 690, 765]
    
    # Create Z3 variables
    num_friends = 9
    met = [Bool(f'met_{i}') for i in range(num_friends)]
    s = [Int(f's_{i}') for i in range(num_friends)]  # start time of meeting
    e = [Int(f'e_{i}') for i in range(num_friends)]  # end time of meeting (s[i] + durations[i])
    
    # Before variables for each pair (i, j) with i < j: true if meeting i is before meeting j
    before = {}
    for i in range(num_friends):
        for j in range(i + 1, num_friends):
            before[(i, j)] = Bool(f'before_{i}_{j}')
    
    # Initialize solver
    opt = Optimize()
    
    # Constraints for each friend
    for i in range(num_friends):
        # If meeting i is scheduled, then:
        #   s[i] must be at least the travel time from Marina (0) to the friend's location
        #   s[i] must be within the friend's window, and the meeting must end before the window closes
        loc_i = loc_index[i]
        opt.add(Implies(met[i], s[i] >= travel_time[0][loc_i]))
        opt.add(Implies(met[i], s[i] >= window_start[i]))
        opt.add(Implies(met[i], e[i] == s[i] + durations[i]))
        opt.add(Implies(met[i], e[i] <= window_end[i]))
    
    # Constraints for pairs of friends
    for i in range(num_friends):
        for j in range(i + 1, num_friends):
            # If both meetings i and j are scheduled, then we enforce the order and travel time
            loc_i = loc_index[i]
            loc_j = loc_index[j]
            b = before[(i, j)]
            # If i is before j, then s[j] >= e[i] + travel_time[loc_i][loc_j]
            # Else, s[i] >= e[j] + travel_time[loc_j][loc_i]
            opt.add(Implies(And(met[i], met[j]),
                            Or(
                                And(b, s[j] >= e[i] + travel_time[loc_i][loc_j]),
                                And(Not(b), s[i] >= e[j] + travel_time[loc_j][loc_i])
                            )))
    
    # Objective: maximize the number of friends met
    total_met = Sum([If(met_i, 1, 0) for met_i in met])
    opt.maximize(total_met)
    
    # Solve
    if opt.check() == sat:
        model = opt.model()
        print("SOLUTION:")
        total = 0
        for i in range(num_friends):
            if model.evaluate(met[i]):
                total += 1
                start_val = model.evaluate(s[i])
                end_val = model.evaluate(e[i])
                # Convert minutes to time string
                start_hour = 9 + start_val.as_long() // 60
                start_min = start_val.as_long() % 60
                end_hour = 9 + end_val.as_long() // 60
                end_min = end_val.as_long() % 60
                friend_names = ["Joshua", "Jeffrey", "Charles", "Joseph", "Elizabeth", "Matthew", "Carol", "Paul", "Rebecca"]
                locations = ["Embarcadero", "Bayview", "Union Square", "Chinatown", "Sunset District", 
                            "Golden Gate Park", "Financial District", "Haight-Ashbury", "Mission District"]
                print(f"Meet {friend_names[i]} at {locations[i]} from {start_hour:02d}:{start_min:02d} to {end_hour:02d}:{end_min:02d}")
        print(f"Total friends met: {total}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()