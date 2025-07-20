from z3 import *

def main():
    # Travel time matrix: [Presidio, Richmond, NorthBeach, Financial, GoldenGate, UnionSquare]
    travel = [
        [0, 7, 18, 23, 12, 22],     # From Presidio
        [7, 0, 17, 22, 9, 21],      # From Richmond
        [17, 18, 0, 8, 22, 7],      # From NorthBeach
        [22, 21, 7, 0, 23, 9],      # From Financial
        [11, 7, 24, 26, 0, 22],     # From GoldenGate
        [24, 20, 10, 9, 22, 0]      # From UnionSquare
    ]

    friends = [
        # (name, loc_index, avail_start, avail_end, min_duration, travel_from_presidio)
        ('Jason', 1, 240, 705, 90, travel[0][1]),
        ('Melissa', 2, 585, 675, 45, travel[0][2]),
        ('Brian', 3, 45, 765, 15, travel[0][3]),
        ('Elizabeth', 4, -15, 750, 105, travel[0][4]),
        ('Laura', 5, 315, 630, 75, travel[0][5])
    ]

    n = len(friends)
    active = [Bool(f[0]) for f in friends]
    start = [Int(f'start_{f[0]}') for f in friends]
    end = [Int(f'end_{f[0]}') for f in friends]

    s = Optimize()

    for i in range(n):
        name, loc_idx, avail_s, avail_e, dur, travel_p = friends[i]
        # If meeting the friend, start time must be at least travel time from Presidio
        s.add(Implies(active[i], start[i] >= travel_p))
        # If availability start time is non-negative, start time must be at least that
        if avail_s >= 0:
            s.add(Implies(active[i], start[i] >= avail_s))
        # Meeting duration constraint
        s.add(Implies(active[i], end[i] == start[i] + dur))
        # End time must be within friend's availability window
        s.add(Implies(active[i], end[i] <= avail_e))

    # Disjunctive constraints for every pair of friends
    for i in range(n):
        for j in range(i + 1, n):
            name_i, loc_i, _, _, _, _ = friends[i]
            name_j, loc_j, _, _, _, _ = friends[j]
            T_ij = travel[loc_i][loc_j]
            T_ji = travel[loc_j][loc_i]
            s.add(Implies(
                And(active[i], active[j]),
                Or(end[i] + T_ij <= start[j], end[j] + T_ji <= start[i])
            ))

    obj = Sum([If(active[i], 1, 0) for i in range(n)])
    s.maximize(obj)

    if s.check() == sat:
        m = s.model()
        active_friends = []
        for i in range(n):
            if m.evaluate(active[i]):
                name = friends[i][0]
                start_val = m.evaluate(start[i])
                end_val = m.evaluate(end[i])
                if isinstance(start_val, IntNumRef) and isinstance(end_val, IntNumRef):
                    start_min = start_val.as_long()
                    end_min = end_val.as_long()
                    start_hour = 9 + start_min // 60
                    start_minute = start_min % 60
                    end_hour = 9 + end_min // 60
                    end_minute = end_min % 60
                    start_str = f"{start_hour}:{start_minute:02d}"
                    end_str = f"{end_hour}:{end_minute:02d}"
                    active_friends.append((name, start_str, end_str))
        print("We meet the following friends:")
        for name, st, et in active_friends:
            print(f"{name}: from {st} to {et}")
        print(f"Total: {len(active_friends)} friends")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()