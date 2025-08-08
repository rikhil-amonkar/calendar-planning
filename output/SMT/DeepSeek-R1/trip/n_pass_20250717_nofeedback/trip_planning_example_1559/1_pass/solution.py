from z3 import *
import json

def main():
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    required_days = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]  # Corresponding to the cities list

    edges = [
        (9,4), (4,9), # Lisbon-Paris
        (2,5), (5,2), # Lyon-Nice
        (7,1), (1,7), # Tallinn-Oslo
        (3,2), (2,3), # Prague-Lyon
        (4,1), (1,4), # Paris-Oslo
        (9,6), (6,9), # Lisbon-Seville
        (3,9), (9,3), # Prague-Lisbon
        (1,5), (5,1), # Oslo-Nice
        (0,4), (4,0), # Valencia-Paris
        (0,9), (9,0), # Valencia-Lisbon
        (4,5), (5,4), # Paris-Nice
        (5,8), (8,5), # Nice-Mykonos
        (4,2), (2,4), # Paris-Lyon
        (0,2), (2,0), # Valencia-Lyon
        (3,1), (1,3), # Prague-Oslo
        (3,4), (4,3), # Prague-Paris
        (6,4), (4,6), # Seville-Paris
        (1,2), (2,1), # Oslo-Lyon
        (3,0), (0,3), # Prague-Valencia
        (9,5), (5,9), # Lisbon-Nice
        (9,1), (1,9), # Lisbon-Oslo
        (0,6), (6,0), # Valencia-Seville
        (9,2), (2,9), # Lisbon-Lyon
        (4,7), (7,4), # Paris-Tallinn
        (3,7), (7,3)  # Prague-Tallinn
    ]

    s = Solver()

    L = [Int(f'L_{i}') for i in range(1, 27)]
    for i in range(26):
        s.add(L[i] >= 0, L[i] < 10)

    fly = [Bool(f'fly_{i}') for i in range(1, 26)]

    for d in range(25):
        edge_cond = Or([And(L[d] == i, L[d+1] == j) for (i, j) in edges])
        s.add(If(fly[d], edge_cond, L[d+1] == L[d]))

    def in_city(day, city_index):
        d_index = day - 1
        return Or(L[d_index] == city_index, And(fly[d_index], L[d_index+1] == city_index))

    for c_index, total in enumerate(required_days):
        total_days = Sum([If(in_city(day, c_index), 1, 0) for day in range(1, 26)])
        s.add(total_days == total)

    s.add(Or(in_city(3, 0), in_city(4, 0)))
    s.add(Or(in_city(13, 1), in_city(14, 1), in_city(15, 1)))
    for day in [5,6,7,8,9]:
        s.add(in_city(day, 6))
    s.add(Or([in_city(day, 8) for day in range(21, 26)]))

    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for day in range(1, 26):
            d_index = day - 1
            start_city_idx = m.eval(L[d_index]).as_long()
            start_city = cities[start_city_idx]
            if m.eval(fly[d_index]):
                end_city_idx = m.eval(L[d_index+1]).as_long()
                end_city = cities[end_city_idx]
                places = sorted([start_city, end_city])
            else:
                places = [start_city]
            itinerary_list.append({"day": day, "place": places})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()