from z3 import *
import json

def main():
    # Define the Z3 variables
    order = [Int('o0'), Int('o1'), Int('o2'), Int('o3'), Int('o4')]
    e0, e1, e2, e3 = Ints('e0 e1 e2 e3')
    s = Solver()

    # City indices mapping
    # 0: Reykjavik, 1: Riga, 2: Warsaw, 3: Istanbul, 4: Krakow
    city_names = {
        0: "Reykjavik",
        1: "Riga",
        2: "Warsaw",
        3: "Istanbul",
        4: "Krakow"
    }
    dur_req = [7, 2, 3, 6, 7]  # durations for cities 0,1,2,3,4

    # Constraints for order: distinct and within [0,4]
    s.add(Distinct(order))
    for i in range(5):
        s.add(order[i] >= 0, order[i] <= 4)

    # End days: 1 <= e0 <= e1 <= e2 <= e3 <= 21
    s.add(e0 >= 1, e0 <= 21)
    s.add(e1 >= e0, e1 <= 21)
    s.add(e2 >= e1, e2 <= 21)
    s.add(e3 >= e2, e3 <= 21)

    # Flight constraints: consecutive cities must have a direct flight
    edges_undir = [(0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4)]
    for i in range(4):
        conds = []
        for a, b in edges_undir:
            conds.append(And(order[i] == a, order[i + 1] == b))
            conds.append(And(order[i] == b, order[i + 1] == a))
        s.add(Or(conds))

    # Duration constraints for each city in the order
    s.add(e0 == dur_req[order[0]])
    s.add(e1 - e0 + 1 == dur_req[order[1]])
    s.add(e2 - e1 + 1 == dur_req[order[2]])
    s.add(e3 - e2 + 1 == dur_req[order[3]])
    s.add(22 - e3 == dur_req[order[4]])  # 21 - e3 + 1 = 22 - e3

    # Event constraints: Riga must start by day 2, Istanbul must start by day 7
    for i in range(5):
        start_day = None
        if i == 0:
            start_day = 1
        elif i == 1:
            start_day = e0
        elif i == 2:
            start_day = e1
        elif i == 3:
            start_day = e2
        else:  # i == 4
            start_day = e3

        s.add(If(order[i] == 1, start_day <= 2, True))
        s.add(If(order[i] == 3, start_day <= 7, True))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        o0_val = m[order[0]].as_long()
        o1_val = m[order[1]].as_long()
        o2_val = m[order[2]].as_long()
        o3_val = m[order[3]].as_long()
        o4_val = m[order[4]].as_long()
        e0_val = m[e0].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()

        order_vals = [o0_val, o1_val, o2_val, o3_val, o4_val]
        itinerary_list = []

        for day in range(1, 22):
            cities = []
            if day <= e0_val:
                cities.append(city_names[order_vals[0]])
            if e0_val <= day <= e1_val:
                cities.append(city_names[order_vals[1]])
            if e1_val <= day <= e2_val:
                cities.append(city_names[order_vals[2]])
            if e2_val <= day <= e3_val:
                cities.append(city_names[order_vals[3]])
            if e3_val <= day <= 21:
                cities.append(city_names[order_vals[4]])
            itinerary_list.append({"day": day, "place": cities})

        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()