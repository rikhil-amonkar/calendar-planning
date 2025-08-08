from z3 import *
import json

def main():
    friends = ["Betty", "Melissa", "Joshua", "Jeffrey", "James", "Anthony", "Timothy", "Emily"]
    locations = ["Russian Hill", "Alamo Square", "Haight-Ashbury", "Marina District", "Bayview", "Chinatown", "Presidio", "Sunset District"]
    available_start = [420, 570, 735, 735, 450, 705, 750, 1170]
    available_end = [1005, 1035, 1140, 1080, 1200, 810, 885, 1290]
    min_duration = [105, 105, 90, 45, 90, 75, 90, 120]

    travel_time_dict = {}
    travel_time_dict[("Union Square", "Russian Hill")] = 13
    travel_time_dict[("Union Square", "Alamo Square")] = 15
    travel_time_dict[("Union Square", "Haight-Ashbury")] = 18
    travel_time_dict[("Union Square", "Marina District")] = 18
    travel_time_dict[("Union Square", "Bayview")] = 15
    travel_time_dict[("Union Square", "Chinatown")] = 7
    travel_time_dict[("Union Square", "Presidio")] = 24
    travel_time_dict[("Union Square", "Sunset District")] = 27

    travel_time_dict[("Russian Hill", "Union Square")] = 10
    travel_time_dict[("Russian Hill", "Alamo Square")] = 15
    travel_time_dict[("Russian Hill", "Haight-Ashbury")] = 17
    travel_time_dict[("Russian Hill", "Marina District")] = 7
    travel_time_dict[("Russian Hill", "Bayview")] = 23
    travel_time_dict[("Russian Hill", "Chinatown")] = 9
    travel_time_dict[("Russian Hill", "Presidio")] = 14
    travel_time_dict[("Russian Hill", "Sunset District")] = 23

    travel_time_dict[("Alamo Square", "Union Square")] = 14
    travel_time_dict[("Alamo Square", "Russian Hill")] = 13
    travel_time_dict[("Alamo Square", "Haight-Ashbury")] = 5
    travel_time_dict[("Alamo Square", "Marina District")] = 15
    travel_time_dict[("Alamo Square", "Bayview")] = 16
    travel_time_dict[("Alamo Square", "Chinatown")] = 15
    travel_time_dict[("Alamo Square", "Presidio")] = 17
    travel_time_dict[("Alamo Square", "Sunset District")] = 16

    travel_time_dict[("Haight-Ashbury", "Union Square")] = 19
    travel_time_dict[("Haight-Ashbury", "Russian Hill")] = 17
    travel_time_dict[("Haight-Ashbury", "Alamo Square")] = 5
    travel_time_dict[("Haight-Ashbury", "Marina District")] = 17
    travel_time_dict[("Haight-Ashbury", "Bayview")] = 18
    travel_time_dict[("Haight-Ashbury", "Chinatown")] = 19
    travel_time_dict[("Haight-Ashbury", "Presidio")] = 15
    travel_time_dict[("Haight-Ashbury", "Sunset District")] = 15

    travel_time_dict[("Marina District", "Union Square")] = 16
    travel_time_dict[("Marina District", "Russian Hill")] = 8
    travel_time_dict[("Marina District", "Alamo Square")] = 15
    travel_time_dict[("Marina District", "Haight-Ashbury")] = 16
    travel_time_dict[("Marina District", "Bayview")] = 27
    travel_time_dict[("Marina District", "Chinatown")] = 15
    travel_time_dict[("Marina District", "Presidio")] = 10
    travel_time_dict[("Marina District", "Sunset District")] = 19

    travel_time_dict[("Bayview", "Union Square")] = 18
    travel_time_dict[("Bayview", "Russian Hill")] = 23
    travel_time_dict[("Bayview", "Alamo Square")] = 16
    travel_time_dict[("Bayview", "Haight-Ashbury")] = 19
    travel_time_dict[("Bayview", "Marina District")] = 27
    travel_time_dict[("Bayview", "Chinatown")] = 19
    travel_time_dict[("Bayview", "Presidio")] = 32
    travel_time_dict[("Bayview", "Sunset District")] = 23

    travel_time_dict[("Chinatown", "Union Square")] = 7
    travel_time_dict[("Chinatown", "Russian Hill")] = 7
    travel_time_dict[("Chinatown", "Alamo Square")] = 17
    travel_time_dict[("Chinatown", "Haight-Ashbury")] = 19
    travel_time_dict[("Chinatown", "Marina District")] = 12
    travel_time_dict[("Chinatown", "Bayview")] = 20
    travel_time_dict[("Chinatown", "Presidio")] = 19
    travel_time_dict[("Chinatown", "Sunset District")] = 29

    travel_time_dict[("Presidio", "Union Square")] = 22
    travel_time_dict[("Presidio", "Russian Hill")] = 14
    travel_time_dict[("Presidio", "Alamo Square")] = 19
    travel_time_dict[("Presidio", "Haight-Ashbury")] = 15
    travel_time_dict[("Presidio", "Marina District")] = 11
    travel_time_dict[("Presidio", "Bayview")] = 31
    travel_time_dict[("Presidio", "Chinatown")] = 21
    travel_time_dict[("Presidio", "Sunset District")] = 15

    travel_time_dict[("Sunset District", "Union Square")] = 30
    travel_time_dict[("Sunset District", "Russian Hill")] = 24
    travel_time_dict[("Sunset District", "Alamo Square")] = 17
    travel_time_dict[("Sunset District", "Haight-Ashbury")] = 15
    travel_time_dict[("Sunset District", "Marina District")] = 21
    travel_time_dict[("Sunset District", "Bayview")] = 22
    travel_time_dict[("Sunset District", "Chinatown")] = 30
    travel_time_dict[("Sunset District", "Presidio")] = 16

    x = [Bool(f'x_{i}') for i in range(8)]
    start = [Int(f'start_{i}') for i in range(8)]
    order = [Int(f'order_{i}') for i in range(8)]

    s = Optimize()

    for i in range(8):
        s.add(If(x[i], And(start[i] >= available_start[i], start[i] + min_duration[i] <= available_end[i]), And(start[i] >= 0, start[i] <= 1500)))
        s.add(If(x[i], And(order[i] >= 0, order[i] < 8), order[i] == -1))

    for i in range(8):
        for j in range(i+1, 8):
            s.add(Implies(And(x[i], x[j]), order[i] != order[j]))

    n = Sum([If(x[i], 1, 0) for i in range(8)])
    for k in range(8):
        count = Sum([If(And(x[i], order[i] == k), 1, 0) for i in range(8)])
        s.add(count == If(k < n, 1, 0))

    for i in range(8):
        loc_i = locations[i]
        travel_from_US = travel_time_dict[("Union Square", loc_i)]
        s.add(Implies(And(x[i], order[i] == 0), start[i] >= 540 + travel_from_US))

    for i in range(8):
        for j in range(8):
            if i == j:
                continue
            loc_i = locations[i]
            loc_j = locations[j]
            travel_ij = travel_time_dict[(loc_i, loc_j)]
            s.add(Implies(And(x[i], x[j], order[j] == order[i] + 1), 
                          start[i] + min_duration[i] + travel_ij <= start[j]))

    s.maximize(n)

    itinerary = []
    if s.check() == sat:
        m = s.model()
        for i in range(8):
            if is_true(m.evaluate(x[i])):
                start_val = m.evaluate(start[i]).as_long()
                end_val = start_val + min_duration[i]
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        itinerary.sort(key=lambda x: x['start_time'])
    else:
        itinerary = []

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()