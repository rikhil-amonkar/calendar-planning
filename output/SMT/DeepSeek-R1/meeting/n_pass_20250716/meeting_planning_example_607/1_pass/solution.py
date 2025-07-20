from z3 import *

def main():
    n_meetings = 7
    n_total = 8  # 7 friends + 1 virtual start
    names = ["Matthew", "Michelle", "Carol", "Stephanie", "Linda", "Jessica", "Karen"]
    districts = [
        "Richmond District",
        "Marina District",
        "North Beach",
        "Union Square",
        "Golden Gate Park",
        "The Castro",
        "Russian Hill"
    ]
    durs = [15, 75, 90, 30, 90, 60, 60]
    available_start = [0, 90, 180, 105, 105, 405, 705]
    available_end = [360, 510, 390, 285, 690, 570, 705]
    
    travel_time_data = [
        ("Sunset District", "Russian Hill", 24),
        ("Sunset District", "The Castro", 17),
        ("Sunset District", "Richmond District", 12),
        ("Sunset District", "Marina District", 21),
        ("Sunset District", "North Beach", 29),
        ("Sunset District", "Union Square", 30),
        ("Sunset District", "Golden Gate Park", 11),
        ("Russian Hill", "Sunset District", 23),
        ("Russian Hill", "The Castro", 21),
        ("Russian Hill", "Richmond District", 14),
        ("Russian Hill", "Marina District", 7),
        ("Russian Hill", "North Beach", 5),
        ("Russian Hill", "Union Square", 11),
        ("Russian Hill", "Golden Gate Park", 21),
        ("The Castro", "Sunset District", 17),
        ("The Castro", "Russian Hill", 18),
        ("The Castro", "Richmond District", 16),
        ("The Castro", "Marina District", 21),
        ("The Castro", "North Beach", 20),
        ("The Castro", "Union Square", 19),
        ("The Castro", "Golden Gate Park", 11),
        ("Richmond District", "Sunset District", 11),
        ("Richmond District", "Russian Hill", 13),
        ("Richmond District", "The Castro", 16),
        ("Richmond District", "Marina District", 9),
        ("Richmond District", "North Beach", 17),
        ("Richmond District", "Union Square", 21),
        ("Richmond District", "Golden Gate Park", 9),
        ("Marina District", "Sunset District", 19),
        ("Marina District", "Russian Hill", 8),
        ("Marina District", "The Castro", 22),
        ("Marina District", "Richmond District", 11),
        ("Marina District", "North Beach", 11),
        ("Marina District", "Union Square", 16),
        ("Marina District", "Golden Gate Park", 18),
        ("North Beach", "Sunset District", 27),
        ("North Beach", "Russian Hill", 4),
        ("North Beach", "The Castro", 22),
        ("North Beach", "Richmond District", 18),
        ("North Beach", "Marina District", 9),
        ("North Beach", "Union Square", 7),
        ("North Beach", "Golden Gate Park", 22),
        ("Union Square", "Sunset District", 26),
        ("Union Square", "Russian Hill", 13),
        ("Union Square", "The Castro", 19),
        ("Union Square", "Richmond District", 20),
        ("Union Square", "Marina District", 18),
        ("Union Square", "North Beach", 10),
        ("Union Square", "Golden Gate Park", 22),
        ("Golden Gate Park", "Sunset District", 10),
        ("Golden Gate Park", "Russian Hill", 19),
        ("Golden Gate Park", "The Castro", 13),
        ("Golden Gate Park", "Richmond District", 7),
        ("Golden Gate Park", "Marina District", 16),
        ("Golden Gate Park", "North Beach", 24),
        ("Golden Gate Park", "Union Square", 22)
    ]
    
    travel_time_dict = {}
    for data in travel_time_data:
        from_loc, to_loc, time = data
        travel_time_dict[(from_loc, to_loc)] = time
    
    T = [[0] * n_total for _ in range(n_total)]
    virtual_start_loc = "Sunset District"
    
    for i in range(n_meetings):
        for j in range(n_meetings):
            from_loc = districts[i]
            to_loc = districts[j]
            T[i][j] = travel_time_dict[(from_loc, to_loc)]
    
    for i in range(n_meetings):
        from_loc = districts[i]
        to_loc = virtual_start_loc
        T[i][7] = travel_time_dict.get((from_loc, to_loc), 0)
    
    for j in range(n_meetings):
        from_loc = virtual_start_loc
        to_loc = districts[j]
        T[7][j] = travel_time_dict.get((from_loc, to_loc), 0)
    
    opt = Optimize()
    
    t = [Int(f't_{i}') for i in range(n_total)]
    b = [Bool(f'b_{i}') for i in range(n_meetings)]
    
    opt.add(t[7] == 0)
    
    for i in range(n_meetings):
        opt.add(Implies(b[i], And(t[i] >= available_start[i], t[i] <= available_end[i])))
        opt.add(Implies(b[i], t[i] >= T[7][i]))
    
    for i in range(n_meetings):
        for j in range(n_meetings):
            if i != j:
                constraint = Or(
                    t[i] + durs[i] + T[i][j] <= t[j],
                    t[j] + durs[j] + T[j][i] <= t[i]
                )
                opt.add(Implies(And(b[i], b[j]), constraint))
    
    objective = Sum([If(b_i, 1, 0) for b_i in b])
    opt.maximize(objective)
    
    if opt.check() == sat:
        m = opt.model()
        count = m.eval(objective)
        print(f"Maximum meetings: {count}")
        for i in range(n_meetings):
            if m.eval(b[i]):
                start_minutes = m.eval(t[i]).as_long()
                hours = 9 + start_minutes // 60
                minutes = start_minutes % 60
                print(f"Meet {names[i]} at {int(hours)}:{minutes:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()