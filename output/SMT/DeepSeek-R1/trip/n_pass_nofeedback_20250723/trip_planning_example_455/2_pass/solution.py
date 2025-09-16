from z3 import *
import json

def main():
    # Cities mapping: 0-Reykjavik, 1-Riga, 2-Warsaw, 3-Istanbul, 4-Krakow
    city_names = {
        0: "Reykjavik",
        1: "Riga",
        2: "Warsaw",
        3: "Istanbul",
        4: "Krakow"
    }
    dur_req = [7, 2, 3, 6, 7]  # durations for cities 0,1,2,3,4

    # Allowed direct flights as undirected edges
    allowed_edges = [
        (0, 2), (2, 0),  # Reykjavik <-> Warsaw
        (1, 2), (2, 1),  # Riga <-> Warsaw
        (1, 3), (3, 1),  # Riga <-> Istanbul
        (2, 3), (3, 2),  # Warsaw <-> Istanbul
        (2, 4), (4, 2),  # Warsaw <-> Krakow
        (3, 4), (4, 3)   # Istanbul <-> Krakow
    ]

    # Z3 variables: order of cities (o0 to o4) and end days (e0 to e3)
    order = [Int(f'o{i}') for i in range(5)]
    e0, e1, e2, e3 = Ints('e0 e1 e2 e3')
    s = Solver()

    # Order constraints: distinct integers between 0 and 4
    s.add([And(ord_i >= 0, ord_i <= 4) for ord_i in order])
    s.add(Distinct(order))

    # End day constraints: 1 <= e0 <= e1 <= e2 <= e3 <= 21
    s.add(e0 >= 1, e0 <= 21)
    s.add(e1 >= e0, e1 <= 21)
    s.add(e2 >= e1, e2 <= 21)
    s.add(e3 >= e2, e3 <= 21)

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(4):
        conds = []
        for edge in allowed_edges:
            conds.append(And(order[i] == edge[0], order[i+1] == edge[1]))
        s.add(Or(conds))

    # Duration constraints using helper function
    def city_dur(city_expr):
        return If(city_expr == 0, dur_req[0],
               If(city_expr == 1, dur_req[1],
               If(city_expr == 2, dur_req[2],
               If(city_expr == 3, dur_req[3], dur_req[4]))))
    
    s.add(e0 == city_dur(order[0]))
    s.add(e1 - e0 + 1 == city_dur(order[1]))
    s.add(e2 - e1 + 1 == city_dur(order[2]))
    s.add(e3 - e2 + 1 == city_dur(order[3]))
    s.add(21 - e3 + 1 == city_dur(order[4]))  # 22 - e3

    # Event constraints: Riga must start by day 2, Istanbul by day 7
    start_days = [1, e0, e1, e2, e3]  # start days for each position in the order
    for i in range(5):
        # Riga (city 1) must start by day 2
        s.add(Implies(order[i] == 1, start_days[i] <= 2))
        # Istanbul (city 3) must start by day 7
        s.add(Implies(order[i] == 3, start_days[i] <= 7))

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract order and end days
        order_vals = [m[ord_i].as_long() for ord_i in order]
        e0_val = m[e0].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()

        # Build itinerary
        itinerary_list = []
        for day in range(1, 22):  # days 1 to 21
            cities = []
            # Check which cities include this day
            if day <= e0_val:
                cities.append(city_names[order_vals[0]])
            if e0_val <= day <= e1_val:
                cities.append(city_names[order_vals[1]])
            if e1_val <= day <= e2_val:
                cities.append(city_names[order_vals[2]])
            if e2_val <= day <= e3_val:
                cities.append(city_names[order_vals[3]])
            if e3_val <= day:
                cities.append(city_names[order_vals[4]])
            itinerary_list.append({"day": day, "place": cities})
        
        # Output as JSON
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()