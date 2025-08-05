from z3 import *
import json

def main():
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    required_days = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]  # Corresponding to the cities list

    directed_edges = [
        (9,4), (4,9), # Lisbon and Paris
        (2,5), (5,2), # Lyon and Nice
        (7,1), (1,7), # Tallinn and Oslo
        (3,2), (2,3), # Prague and Lyon
        (4,1), (1,4), # Paris and Oslo
        (9,6), (6,9), # Lisbon and Seville
        (3,9), (9,3), # Prague and Lisbon
        (1,5), (5,1), # Oslo and Nice
        (0,4), (4,0), # Valencia and Paris
        (0,9), (9,0), # Valencia and Lisbon
        (4,5), (5,4), # Paris and Nice
        (5,8), (8,5), # Nice and Mykonos
        (4,2), (2,4), # Paris and Lyon
        (0,2), (2,0), # Valencia and Lyon
        (3,1), (1,3), # Prague and Oslo
        (3,4), (4,3), # Prague and Paris
        (6,4), (4,6), # Seville and Paris
        (1,2), (2,1), # Oslo and Lyon
        (3,0), (0,3), # Prague and Valencia
        (9,5), (5,9), # Lisbon and Nice
        (9,1), (1,9), # Lisbon and Oslo
        (0,6), (6,0), # Valencia and Seville
        (9,2), (2,9), # Lisbon and Lyon
        (4,7), (7,4), # Paris and Tallinn
        (3,7), (7,3)  # Prague and Tallinn
    ]

    s = Solver()

    L = [Int(f'L_{i}') for i in range(25)]
    for i in range(25):
        s.add(L[i] >= 0, L[i] < 10)

    fly = [Bool(f'fly_{i}') for i in range(24)]

    for i in range(24):
        edge_constraints = []
        for a, b in directed_edges:
            edge_constraints.append(And(L[i] == a, L[i+1] == b))
        s.add(If(fly[i], Or(edge_constraints), L[i] == L[i+1]))

    def in_city(day, city_index):
        d0 = day - 1
        if day < 25:
            return Or(L[d0] == city_index, And(fly[d0], L[d0+1] == city_index))
        else:
            return L[24] == city_index

    for c_index, total in enumerate(required_days):
        total_days = 0
        for day in range(1, 26):
            total_days += If(in_city(day, c_index), 1, 0)
        s.add(total_days == total)

    valencia_constraint = Or(in_city(3, 0), in_city(4, 0))
    oslo_constraint = Or(in_city(13, 1), in_city(14, 1), in_city(15, 1))
    seville_constraint = Or([in_city(day, 6) for day in range(5, 10)])
    mykonos_constraint = Or([in_city(day, 8) for day in range(21, 26)])

    s.add(valencia_constraint, oslo_constraint, seville_constraint, mykonos_constraint)

    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for day in range(1, 26):
            d0 = day - 1
            city_indices = set()
            start_city_idx = m.eval(L[d0]).as_long()
            city_indices.add(start_city_idx)
            if day < 25:
                if m.eval(fly[d0]):
                    next_city_idx = m.eval(L[d0+1]).as_long()
                    city_indices.add(next_city_idx)
            city_names = sorted([cities[idx] for idx in city_indices])
            itinerary_list.append({"day": day, "place": city_names})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()