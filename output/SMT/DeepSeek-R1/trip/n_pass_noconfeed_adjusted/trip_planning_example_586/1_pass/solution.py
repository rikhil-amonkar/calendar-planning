from z3 import *
import json

def main():
    # Cities: Prague, Lyon, Frankfurt, Helsinki, Naples
    cities = ['Prague', 'Lyon', 'Frankfurt', 'Helsinki', 'Naples']
    n_days = 12
    n_cities = 5

    # Direct flights (symmetric)
    direct_flights = [(0,1), (0,2), (0,3), (1,2), (2,3), (3,4), (2,4)]
    allowed_pairs = []
    for (a, b) in direct_flights:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))

    # Solver
    s = Solver()

    # Variables
    start_city = [Int('start_city_%d' % i) for i in range(1, n_days+1)]
    flight_taken = [Bool('flight_taken_%d' % i) for i in range(1, n_days+1)]
    flight_dest = [Int('flight_dest_%d' % i) for i in range(1, n_days+1)]

    # Constraints for each day
    for i in range(1, n_days+1):
        # start_city must be between 0 and 4
        s.add(start_city[i-1] >= 0, start_city[i-1] <= 4)
        # If flight taken, then flight_dest must be valid and different from start_city, and direct flight must exist
        if i == 2:
            # We fix day2: flight taken to Helsinki
            s.add(flight_taken[i-1] == True)
            s.add(flight_dest[i-1] == 3)  # Helsinki
        else:
            s.add(Implies(flight_taken[i-1], 
                          And(flight_dest[i-1] >= 0, flight_dest[i-1] <= 4,
                              start_city[i-1] != flight_dest[i-1],
                              Or([And(start_city[i-1] == a, flight_dest[i-1] == b) for (a, b) in allowed_pairs])
                          )))

    # Start city for day1 is Prague
    s.add(start_city[0] == 0)  # Prague

    # Relationship between days
    for i in range(2, n_days+1):
        s.add(start_city[i-1] == If(flight_taken[i-2], flight_dest[i-2], start_city[i-2]))

    # Total days per city
    total_days = [0] * n_cities
    for c in range(n_cities):
        total_days[c] = Sum([If(start_city[i] == c, 1, 0) for i in range(n_days)]) + \
                        Sum([If(And(flight_taken[i], flight_dest[i] == c), 1, 0) for i in range(n_days)])
    s.add(total_days[0] == 2)  # Prague
    s.add(total_days[1] == 3)  # Lyon
    s.add(total_days[2] == 3)  # Frankfurt
    s.add(total_days[3] == 4)  # Helsinki
    s.add(total_days[4] == 4)  # Naples

    # Must be in Helsinki on days 2,3,4,5
    # Day2: already handled by flight to Helsinki
    # For day3,4,5: must be in Helsinki (either start there or fly there)
    for d in [3,4,5]:
        day_index = d-1
        s.add(Or(start_city[day_index] == 3, 
                 And(flight_taken[day_index], flight_dest[day_index] == 3)))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Evaluate ending city for each day
        ending_cities = []
        for i in range(n_days):
            if m.evaluate(flight_taken[i]):
                ending_city_val = m.evaluate(flight_dest[i])
            else:
                ending_city_val = m.evaluate(start_city[i])
            ending_cities.append(ending_city_val.as_long())
        
        # Group consecutive days with same ending city
 itinerary = []
        start_index = 0
        current_city = ending_cities[0]
        for i in range(1, n_days):
            if ending_cities[i] != current_city:
                if start_index == i-1:
                    day_range = f"Day {start_index+1}"
                else:
                    day_range = f"Day {start_index+1}-{i}"
                itinerary.append({"day_range": day_range, "place": cities[current_city]})
                start_index = i
                current_city = ending_cities[i]
        if start_index == n_days-1:
            day_range = f"Day {n_days}"
        else:
            day_range = f"Day {start_index+1}-{n_days}"
        itinerary.append({"day_range": day_range, "place": cities[current_city]})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()