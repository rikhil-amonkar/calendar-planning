from z3 import *

def main():
    # Travel times matrix: 0=Castro, 1=Bayview, 2=PacificHeights, 3=AlamoSquare, 4=FishermanWharf, 5=GoldenGatePark
    T = [
        [0, 19, 16, 8, 24, 11],
        [20, 0, 23, 16, 25, 22],
        [16, 22, 0, 10, 13, 15],
        [8, 16, 10, 0, 19, 9],
        [26, 26, 12, 20, 0, 25],
        [13, 23, 16, 10, 24, 0]
    ]
    # Availability windows in minutes from 9:00 AM: [start, end]
    window_start = [0, 0, 570, 45, 0, 0]  # Index 0 unused (Castro)
    window_end = [0, 225, 765, 735, 750, 585]  # Index 0 unused

    # Initialize Z3 variables
    order = [Int('order_%d' % i) for i in range(5)]
    s = [Int('s_%d' % i) for i in range(5)]  # Start times
    e = [Int('e_%d' % i) for i in range(5)]  # End times

    # Constraints list
    constraints = []

    # Order variables: 0 means skip, 1-5 represent friends
    for i in range(5):
        constraints.append(And(order[i] >= 0, order[i] <= 5))

    # Contiguous zeros: if a position is skipped, subsequent positions must be skipped
    for i in range(4):
        constraints.append(If(order[i] == 0, order[i+1] == 0, True))

    # No duplicate friends
    for i in range(5):
        for j in range(i+1, 5):
            constraints.append(If(And(order[i] != 0, order[j] != 0), order[i] != order[j], True))

    # Helper functions for travel time and window lookups
    def travel_time(fr, to):
        cases = []
        for i in range(6):
            for j in range(6):
                cases.append((And(fr == i, to == j), T[i][j]))
        return If(cases)

    def win_start(loc):
        cases = []
        for i in range(6):
            cases.append((loc == i, window_start[i]))
        return If(cases)

    def win_end(loc):
        cases = []
        for i in range(6):
            cases.append((loc == i, window_end[i]))
        return If(cases)

    # Time constraints for each position
    for i in range(5):
        loc = order[i]
        if i == 0:
            arrival_time = travel_time(0, loc)  # Travel from Castro
        else:
            arrival_time = e[i-1] + travel_time(order[i-1], loc)
        
        constraints.append(If(loc != 0,
                             And(
                                 s[i] >= arrival_time,
                                 s[i] >= win_start(loc),
                                 e[i] == s[i] + 90,
                                 e[i] <= win_end(loc)
                             ),
                             True))

    # Count the number of friends met
    met_friends = []
    for j in range(1, 6):  # Friends 1 to 5
        met_f = Or([order[i] == j for i in range(5)])
        met_friends.append(met_f)
    total_met = Sum([If(m, 1, 0) for m in met_friends])

    # Set up and run the optimizer
    opt = Optimize()
    opt.add(constraints)
    opt.maximize(total_met)
    
    if opt.check() == sat:
        m = opt.model()
        total_met_val = m.eval(total_met).as_long()
        print(f"SOLUTION: We can meet {total_met_val} friends.")
        schedule = []
        for i in range(5):
            loc_val = m.eval(order[i]).as_long()
            if loc_val != 0:
                start_min = m.eval(s[i]).as_long()
                end_min = start_min + 90
                start_hr = 9 + start_min // 60
                start_min %= 60
                end_hr = 9 + end_min // 60
                end_min %= 60
                friend_name = ["Rebecca (Bayview)", "Amanda (Pacific Heights)", "James (Alamo Square)", 
                               "Sarah (Fisherman's Wharf)", "Melissa (Golden Gate Park)"][loc_val-1]
                schedule.append((i, friend_name, f"{start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}"))
        if schedule:
            print("Schedule:")
            for pos, friend, time in schedule:
                print(f"  Position {pos+1}: Meet {friend} from {time}")
    else:
        print("SOLUTION: No feasible schedule found.")

if __name__ == "__main__":
    main()