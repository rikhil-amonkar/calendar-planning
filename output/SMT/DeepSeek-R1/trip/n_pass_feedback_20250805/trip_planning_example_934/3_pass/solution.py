from z3 import *
import json

def main():
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    req = [5, 2, 3, 5, 2, 4, 2]  # days required for each city
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

    # Constraints for the first city in the sequence
    for i in range(7):
        s.add(Implies(seq[0] == i, city_start[i] == 1))
        s.add(Implies(seq[0] == i, city_end[i] == 1 + req[i] - 1))

    # Constraints for subsequent cities
    for k in range(1, 7):
        for i in range(7):
            for j in range(7):
                s.add(Implies(And(seq[k-1] == j, seq[k] == i), city_start[i] == city_end[j]))
            s.add(Implies(seq[k] == i, city_end[i] == city_start[i] + req[i] - 1))

    # Meeting constraints
    # Brussels (index 0) must include at least one day between 7 and 11
    s.add(city_start[0] <= 11, city_end[0] >= 7)
    # Budapest (index 4) must include at least one day between 16 and 17
    s.add(city_start[4] <= 17, city_end[4] >= 16)
    # Riga (index 5) must include at least one day between 4 and 7
    s.add(city_start[5] <= 7, city_end[5] >= 4)

    # Flight constraints: consecutive cities must have a direct flight
    for k in range(6):  # 6 transitions between 7 cities
        flight_cond = False
        for (a, b) in flight_pairs:
            flight_cond = Or(flight_cond, 
                             And(seq[k] == a, seq[k+1] == b),
                             And(seq[k] == b, seq[k+1] == a))
        s.add(flight_cond)

    # Total trip must end on day 17
    s.add(city_end[seq[6]] == 17)

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract the sequence
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(7)]
        # Extract start and end days for each city
        start_val = [m.evaluate(city_start[i]).as_long() for i in range(7)]
        end_val = [m.evaluate(city_end[i]).as_long() for i in range(7)]
        
        # Build itinerary per day
        itinerary = []
        for day in range(1, 18):  # Days 1 to 17
            cities_today = []
            for i in range(7):
                if start_val[i] <= day <= end_val[i]:
                    cities_today.append(cities[i])
            itinerary.append({"day": day, "city": cities_today})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()