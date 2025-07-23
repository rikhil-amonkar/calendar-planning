from z3 import *

def solve_scheduling():
    # Cities
    cities = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 17

    # Direct flights: adjacency matrix
    direct_flights = [
        [False] * n_cities for _ in range(n_cities)
    ]
    # Populate direct flights
    connections = [
        ('Brussels', 'Venice'), ('Brussels', 'London'), ('Brussels', 'Lisbon'),
        ('Brussels', 'Reykjavik'), ('Brussels', 'Madrid'),
        ('Venice', 'Santorini'), ('Venice', 'Lisbon'), ('Venice', 'London'), ('Venice', 'Madrid'),
        ('London', 'Madrid'), ('London', 'Santorini'), ('London', 'Reykjavik'), ('London', 'Lisbon'),
        ('Lisbon', 'Reykjavik'), ('Lisbon', 'Madrid'),
        ('Reykjavik', 'Madrid'),
        ('Santorini', 'Madrid')
    ]
    for a, b in connections:
        i = city_map[a]
        j = city_map[b]
        direct_flights[i][j] = True
        direct_flights[j][i] = True

    # Create Z3 variables: day i is city j
    X = [Int(f"day_{i}") for i in range(n_days)]
    s = Solver()

    # Each day must be a valid city index
    for i in range(n_days):
        s.add(And(X[i] >= 0, X[i] < n_cities))

    # Flight transitions: consecutive days must have a direct flight or be the same city
    for i in range(n_days - 1):
        current_city = X[i]
        next_city = X[i + 1]
        # Check if there's a direct flight between current_city and next_city
        flight_exists = Or([And(current_city == j, next_city == k) 
                          for j in range(n_cities) 
                          for k in range(n_cities) 
                          if direct_flights[j][k]])
        s.add(Or(current_city == next_city, flight_exists))

    # Fixed constraints
    # Brussels days 1 and 2 (0-based days 0 and 1)
    s.add(X[0] == city_map['Brussels'])
    s.add(X[1] == city_map['Brussels'])

    # Venice between day 5 and 7 (0-based days 4-6), 3 days total
    s.add(Or(
        X[4] == city_map['Venice'],
        X[5] == city_map['Venice'],
        X[6] == city_map['Venice']
    ))
    venice_days = Sum([If(X[i] == city_map['Venice'], 1, 0) for i in range(n_days)])
    s.add(venice_days == 3)

    # London 3 days
    london_days = Sum([If(X[i] == city_map['London'], 1, 0) for i in range(n_days)])
    s.add(london_days == 3)

    # Lisbon 4 days
    lisbon_days = Sum([If(X[i] == city_map['Lisbon'], 1, 0) for i in range(n_days)])
    s.add(lisbon_days == 4)

    # Reykjavik 3 days
    reykjavik_days = Sum([If(X[i] == city_map['Reykjavik'], 1, 0) for i in range(n_days)])
    s.add(reykjavik_days == 3)

    # Santorini 3 days
    santorini_days = Sum([If(X[i] == city_map['Santorini'], 1, 0) for i in range(n_days)])
    s.add(santorini_days == 3)

    # Madrid 5 days, including days 7-11 (0-based days 6-10)
    madrid_days = Sum([If(X[i] == city_map['Madrid'], 1, 0) for i in range(n_days)])
    s.add(madrid_days == 5)
    s.add(Or([X[i] == city_map['Madrid'] for i in range(6, 11)]))

    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_index = m.evaluate(X[i]).as_long()
            itinerary.append({"day": i + 1, "place": cities[city_index]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_scheduling()
print(result)