from z3 import *

def main():
    # Define city indices
    cities_dict = {
        "Bucharest": 0,
        "Venice": 1,
        "Prague": 2,
        "Frankfurt": 3,
        "Zurich": 4,
        "Florence": 5,
        "Tallinn": 6
    }
    city_names = {v: k for k, v in cities_dict.items()}
    
    # Directed flight edges (from, to)
    edges = [
        (2, 6), (6, 2),  # Prague <-> Tallinn
        (2, 4), (4, 2),  # Prague <-> Zurich
        (5, 2), (2, 5),  # Florence <-> Prague
        (3, 0), (0, 3),  # Frankfurt <-> Bucharest
        (3, 1), (1, 3),  # Frankfurt <-> Venice
        (2, 0), (0, 2),  # Prague <-> Bucharest
        (0, 4), (4, 0),  # Bucharest <-> Zurich
        (6, 3), (3, 6),  # Tallinn <-> Frankfurt
        (4, 5),           # Zurich -> Florence
        (3, 4), (4, 3),   # Frankfurt <-> Zurich
        (4, 1), (1, 4),   # Zurich <-> Venice
        (5, 3), (3, 5),   # Florence <-> Frankfurt
        (2, 3), (3, 2),   # Prague <-> Frankfurt
        (6, 4), (4, 6)    # Tallinn <-> Zurich
    ]
    
    # Required days per city
    required_days = [3, 5, 4, 5, 5, 5, 5]  # [Bucharest, Venice, Prague, Frankfurt, Zurich, Florence, Tallinn]
    
    # Create Z3 variables: 27 variables (city0 to city26)
    cities = [Int('city_%d' % i) for i in range(27)]
    
    s = Solver()
    
    # Each city variable must be in [0, 6]
    for c in cities:
        s.add(And(c >= 0, c <= 6))
    
    # Flight constraints for each day (1 to 26)
    for i in range(1, 27):
        # Either stay in the same city or take a direct flight
        stay = (cities[i-1] == cities[i])
        flight_conds = []
        for a, b in edges:
            flight_conds.append(And(cities[i-1] == a, cities[i] == b))
        s.add(Or(stay, Or(flight_conds)))
    
    # Total days per city constraint
    for c in range(7):
        total = 0
        for i in range(1, 27):
            total += If(Or(cities[i-1] == c, cities[i] == c), 1, 0)
        s.add(total == required_days[c])
    
    # Event constraints
    # Venice (1) must be visited between day 22 and 26
    venice_days = []
    for i in [22, 23, 24, 25, 26]:
        venice_days.append(Or(cities[i-1] == 1, cities[i] == 1))
    s.add(Or(venice_days))
    
    # Frankfurt (3) between day 12 and 16
    frankfurt_days = []
    for i in [12, 13, 14, 15, 16]:
        frankfurt_days.append(Or(cities[i-1] == 3, cities[i] == 3))
    s.add(Or(frankfurt_days))
    
    # Tallinn (6) between day 8 and 12
    tallinn_days = []
    for i in [8, 9, 10, 11, 12]:
        tallinn_days.append(Or(cities[i-1] == 6, cities[i] == 6))
    s.add(Or(tallinn_days))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 27):
            city_index = model.evaluate(cities[day]).as_long()
            itinerary.append({"day": day, "place": city_names[city_index]})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()