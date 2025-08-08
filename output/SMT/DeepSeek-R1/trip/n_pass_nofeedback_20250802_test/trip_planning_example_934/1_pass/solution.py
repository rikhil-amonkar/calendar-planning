from z3 import *
import json

def main():
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    city_dict = { city: idx for idx, city in enumerate(cities) }
    req_days = [5, 2, 3, 5, 2, 4, 2]  # in the order of cities

    bidirectional_pairs = [
        ('Brussels', 'Valencia'),
        ('Rome', 'Valencia'),
        ('Brussels', 'Geneva'),
        ('Rome', 'Geneva'),
        ('Dubrovnik', 'Geneva'),
        ('Valencia', 'Geneva'),
        ('Geneva', 'Budapest'),
        ('Riga', 'Brussels'),
        ('Rome', 'Budapest'),
        ('Rome', 'Brussels'),
        ('Brussels', 'Budapest'),
        ('Dubrovnik', 'Rome')
    ]
    directed_edges_set = set()
    for a, b in bidirectional_pairs:
        i = city_dict[a]
        j = city_dict[b]
        directed_edges_set.add((i, j))
        directed_edges_set.add((j, i))
    directed_edges_set.add((city_dict['Rome'], city_dict['Riga']))

    num_days = 17
    s = Solver()
    start = [Int(f'start_{d}') for d in range(num_days)]
    flight = [Int(f'flight_{d}') for d in range(num_days)]

    for d in range(num_days):
        s.add(start[d] >= 0, start[d] <= 6)
        s.add(flight[d] >= 0, flight[d] <= 7)

    for d in range(num_days):
        condition = (flight[d] != 7)
        options = []
        for (i, j) in directed_edges_set:
            options.append(And(start[d] == i, flight[d] == j))
        s.add(If(condition, Or(options), True))

    for d in range(num_days - 1):
        s.add(start[d+1] == If(flight[d] != 7, flight[d], start[d]))

    for c in range(7):
        total = 0
        for d in range(num_days):
            total += If(Or(start[d] == c, flight[d] == c), 1, 0)
        s.add(total == req_days[c])

    brussels_constraint = Or([Or(start[d] == 0, flight[d] == 0) for d in range(6, 11)])
    s.add(brussels_constraint)

    riga_constraint = Or([Or(start[d] == 5, flight[d] == 5) for d in range(3, 7)])
    s.add(riga_constraint)

    budapest_constraint = Or([Or(start[d] == 4, flight[d] == 4) for d in [15, 16]])
    s.add(budapest_constraint)

    flight_count = Sum([If(flight[d] != 7, 1, 0) for d in range(num_days)])
    s.add(flight_count == 6)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(num_days):
            s_val = model.evaluate(start[d]).as_long()
            f_val = model.evaluate(flight[d]).as_long()
            start_city = cities[s_val]
            if f_val == 7:
                places = [start_city]
            else:
                flight_city = cities[f_val]
                places = [start_city, flight_city]
            itinerary.append({"day": d+1, "place": places})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()