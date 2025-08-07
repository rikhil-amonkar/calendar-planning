from z3 import *
import json

def main():
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    req = [5, 2, 3, 5, 2, 4, 2]
    flight_pairs = [
        (0, 6), (1, 6), (0, 3), (1, 3), (2, 3), (6, 3), (1, 5),
        (3, 4), (5, 0), (1, 4), (0, 1), (0, 4), (2, 1)
    ]

    s = Solver()

    # Sequence: which city is at each position (0 to 6)
    seq = [Int(f'seq_{i}') for i in range(7)]
    for i in range(7):
        s.add(seq[i] >= 0, seq[i] <= 6)
    s.add(Distinct(seq))

    # Start and end days for each city
    city_start = [Int(f'city_start_{i}') for i in range(7)]
    city_end = [Int(f'city_end_{i}') for i in range(7)]

    # First city starts at day 1
    for i in range(7):
        s.add(Implies(seq[0] == i, city_start[i] == 1))
        s.add(Implies(seq[0] == i, city_end[i] == req[i]))

    # Subsequent cities start where the previous city ended
    for k in range(1, 7):
        for i in range(7):
            for j in range(7):
                s.add(Implies(
                    And(seq[k-1] == j, seq[k] == i),
                    city_start[i] == city_end[j]
                ))
            s.add(Implies(
                seq[k] == i,
                city_end[i] == city_start[i] + req[i] - 1
            ))

    # Meeting constraints
    s.add(city_start[0] <= 11, city_end[0] >= 7)   # Brussels
    s.add(city_start[4] <= 17, city_end[4] >= 16)  # Budapest
    s.add(city_start[5] <= 7, city_end[5] >= 4)    # Riga

    # Flight constraints for consecutive cities
    for k in range(6):
        flight_cond = False
        for a, b in flight_pairs:
            flight_cond = Or(flight_cond,
                             And(seq[k] == a, seq[k+1] == b),
                             And(seq[k] == b, seq[k+1] == a))
        s.add(flight_cond)

    # Last city must end on day 17 (using symbolic lookup)
    last_city_end = Int('last_city_end')
    s.add(last_city_end == 17)
    s.add(last_city_end == If(seq[6] == 0, city_end[0],
                If(seq[6] == 1, city_end[1],
                If(seq[6] == 2, city_end[2],
                If(seq[6] == 3, city_end[3],
                If(seq[6] == 4, city_end[4],
                If(seq[6] == 5, city_end[5],
                city_end[6]))))))

    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(7)]
        start_val = [m.evaluate(city_start[i]).as_long() for i in range(7)]
        end_val = [m.evaluate(city_end[i]).as_long() for i in range(7)]
        
        itinerary = []
        for day in range(1, 18):
            cities_today = []
            for i in range(7):
                if start_val[i] <= day <= end_val[i]:
                    cities_today.append(cities[i])
            itinerary.append({"day": day, "city": cities_today})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()