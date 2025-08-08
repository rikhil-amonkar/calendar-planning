from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    am_pm = 'AM' if hours < 12 else 'PM'
    hours12 = hours % 12
    if hours12 == 0:
        hours12 = 12
    return f"{hours12}:{mins:02d} {am_pm}"

def main():
    names = ["Emily", "Helen", "Kimberly", "James", "Linda", "Paul", "Anthony", "Nancy", "William", "Margaret"]
    neighborhoods = [
        "Pacific Heights",
        "North Beach",
        "Golden Gate Park",
        "Embarcadero",
        "Haight-Ashbury",
        "Fisherman's Wharf",
        "Mission District",
        "Alamo Square",
        "Bayview",
        "Richmond District"
    ]
    starts_avail = [555, 825, 1125, 630, 450, 885, 480, 510, 1050, 915]
    ends_avail = [825, 1125, 1275, 690, 1155, 1125, 885, 825, 1230, 1095]
    min_durations = [120, 30, 75, 30, 15, 90, 105, 120, 120, 45]
    travel_start = [7, 5, 21, 8, 17, 7, 16, 15, 23, 14]
    travel_matrix = [
        [0, 9, 15, 10, 11, 13, 15, 10, 22, 12],
        [8, 0, 22, 6, 18, 5, 18, 16, 25, 18],
        [16, 23, 0, 25, 7, 24, 17, 9, 23, 7],
        [11, 5, 25, 0, 21, 6, 20, 19, 21, 21],
        [12, 19, 7, 20, 0, 23, 11, 5, 18, 10],
        [12, 6, 25, 8, 22, 0, 22, 21, 26, 18],
        [16, 17, 17, 19, 12, 22, 0, 11, 14, 20],
        [10, 15, 9, 16, 5, 19, 10, 0, 16, 11],
        [23, 22, 22, 19, 19, 25, 13, 16, 0, 25],
        [10, 17, 9, 19, 10, 18, 20, 13, 27, 0]
    ]

    n = len(names)

    opt = Optimize()
    met = [Bool(f'met_{i}') for i in range(n)]
    next_vars = [Int(f'next_{i}') for i in range(n)]
    in_degree = [Int(f'in_degree_{i}') for i in range(n)]
    arrival = [Int(f'arrival_{i}') for i in range(n)]
    start_t = [Int(f'start_{i}') for i in range(n)]
    end_t = [Int(f'end_{i}') for i in range(n)]

    for i in range(n):
        opt.add(If(met[i], 
                   Or(And(next_vars[i] >= 0, next_vars[i] < n, next_vars[i] != i), next_vars[i] == n),
                   next_vars[i] == n))
        opt.add(If(met[i],
                   And(arrival[i] <= start_t[i],
                       start_t[i] >= starts_avail[i],
                       end_t[i] == start_t[i] + min_durations[i],
                       end_t[i] <= ends_avail[i]),
                   True))

    for i in range(n):
        opt.add(in_degree[i] == Sum([If(And(met[j], next_vars[j] == i), 1, 0) for j in range(n)]))

    start_count = Sum([If(And(met[i], in_degree[i] == 0), 1, 0) for i in range(n)])
    opt.add(start_count == 1)

    for i in range(n):
        opt.add(If(met[i], 
                   Or(in_degree[i] == 0, in_degree[i] == 1),
                   in_degree[i] == 0))

    for i in range(n):
        opt.add(If(And(met[i], in_degree[i] == 0),
                    arrival[i] == 540 + travel_start[i],
                    True))

    for i in range(n):
        for j in range(n):
            opt.add(Implies(And(met[i], met[j], next_vars[i] == j),
                             arrival[j] == end_t[i] + travel_matrix[i][j]))

    num_met = Sum([If(met[i], 1, 0) for i in range(n)])
    num_edges = Sum([If(And(met[i], next_vars[i] != n), 1, 0) for i in range(n)])
    opt.add(num_edges == If(num_met > 0, num_met - 1, 0))

    for i in range(n):
        for j in range(n):
            opt.add(Implies(And(met[i], next_vars[i] == j), met[j]))

    opt.maximize(num_met)

    if opt.check() == sat:
        m = opt.model()
        met_list = [is_true(m.evaluate(met[i])) for i in range(n)]
        start_index = None
        for i in range(n):
            if met_list[i]:
                in_deg = m.evaluate(in_degree[i]).as_long()
                if in_deg == 0:
                    start_index = i
                    break
        if start_index is None:
            print("SOLUTION:\nYou will meet 0 friends.")
        else:
            order = []
            current = start_index
            while current < n:
                order.append(current)
                next_val = m.evaluate(next_vars[current]).as_long()
                if next_val == n:
                    break
                current = next_val
            n_met = len(order)
            print(f"SOLUTION:\nYou will meet {n_met} friends: {', '.join(names[i] for i in order)}")
            print("Schedule:")
            for i in order:
                start_val = m.evaluate(start_t[i]).as_long()
                end_val = m.evaluate(end_t[i]).as_long()
                start_str = min_to_time(start_val)
                end_str = min_to_time(end_val)
                print(f"{names[i]} at {neighborhoods[i]} from {start_str} to {end_str}")
    else:
        print("SOLUTION:\nYou will meet 0 friends.")

if __name__ == "__main__":
    main()