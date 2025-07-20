from z3 import *
import time

def main():
    # Convert friend availability times to minutes from 9:00 AM
    friends = [
        ("Charles", "Presidio", (13*60+15) - (9*60), (15*60) - (9*60), 105),
        ("Robert", "Nob Hill", (13*60+15) - (9*60), (17*60+30) - (9*60), 90),
        ("Nancy", "Pacific Heights", (14*60+45) - (9*60), (22*60) - (9*60), 105),
        ("Brian", "Mission District", (15*60+30) - (9*60), (22*60) - (9*60), 60),
        ("Kimberly", "Marina District", (17*60) - (9*60), (19*60+45) - (9*60), 75),
        ("David", "North Beach", (14*60+45) - (9*60), (16*60+30) - (9*60), 75),
        ("William", "Russian Hill", (12*60+30) - (9*60), (19*60+15) - (9*60), 120),
        ("Jeffrey", "Richmond District", (12*60) - (9*60), (19*60+15) - (9*60), 45),
        ("Karen", "Embarcadero", (14*60+15) - (9*60), (20*60+45) - (9*60), 60),
        ("Joshua", "Alamo Square", (18*60+45) - (9*60), (22*60) - (9*60), 60)
    ]

    travel_time = {
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Alamo Square"): 15,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Alamo Square"): 15,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Alamo Square"): 13,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16
    }

    opt = Optimize()
    n = 10

    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    end = [Real(f'end_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    m = Int('m')
    opt.add(m == Sum([If(meet[i], 1, 0) for i in range(n)]))

    for i in range(n):
        name, loc, avail_start, avail_end, min_dur = friends[i]
        opt.add(If(meet[i], 
                 And(start[i] >= avail_start, 
                     end[i] <= avail_end, 
                     end[i] - start[i] >= min_dur,
                     order[i] >= 0,
                     order[i] < m),
                 And(order[i] == -1, start[i] == 0, end[i] == 0)))

    for k in range(0, 10):
        opt.add(Implies(k < m, Or([And(meet[i], order[i] == k) for i in range(n)])))

    for i in range(n):
        name_i, loc_i, _, _, _ = friends[i]
        opt.add(Implies(And(meet[i], order[i] == 0), 
                     start[i] >= travel_time[("Sunset District", loc_i)]))

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            name_i, loc_i, _, _, _ = friends[i]
            name_j, loc_j, _, _, _ = friends[j]
            opt.add(Implies(And(meet[i], meet[j], order[j] == order[i] + 1),
                          start[j] >= end[i] + travel_time[(loc_i, loc_j)]))

    opt.maximize(m)

    start_time = time.time()
    result = opt.check()
    end_time = time.time()
    print(f"Solving took {end_time - start_time:.2f} seconds")

    if result == sat:
        model = opt.model()
        total_met = model.eval(m).as_long()
        schedule = []
        for i in range(n):
            if model.eval(meet[i]):
                name = friends[i][0]
                s_val = model.eval(start[i])
                e_val = model.eval(end[i])
                o_val = model.eval(order[i])
                s_min = s_val.as_long()
                e_min = e_val.as_long()
                s_time = f"{9 + s_min // 60}:{str(s_min % 60).zfill(2)}"
                e_time = f"{9 + e_min // 60}:{str(e_min % 60).zfill(2)}"
                schedule.append((o_val, name, s_time, e_time))
        schedule.sort(key=lambda x: x[0])
        print(f"Total friends met: {total_met}")
        for order_val, name, s_time, e_time in schedule:
            print(f"Meet {name} from {s_time} to {e_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()