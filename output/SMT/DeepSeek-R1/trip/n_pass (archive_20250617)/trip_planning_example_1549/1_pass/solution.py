from z3 import *

def main():
    # Cities and their required days
    cities = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }
    
    # Fixed stays
    fixed_stays = [
        ("Riga", 5, 8),
        ("Tallinn", 18, 20),
        ("Milan", 24, 26)
    ]
    
    # Direct flights
    direct_flights = {
        ("Riga", "Prague"),
        ("Stockholm", "Milan"),
        ("Riga", "Milan"),
        ("Lisbon", "Stockholm"),
        ("Stockholm", "Santorini"),
        ("Naples", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Naples", "Milan"),
        ("Lisbon", "Naples"),
        ("Riga", "Tallinn"),
        ("Tallinn", "Prague"),
        ("Stockholm", "Warsaw"),
        ("Riga", "Warsaw"),
        ("Lisbon", "Riga"),
        ("Riga", "Stockholm"),
        ("Lisbon", "Porto"),
        ("Lisbon", "Prague"),
        ("Milan", "Porto"),
        ("Prague", "Milan"),
        ("Lisbon", "Milan"),
        ("Warsaw", "Porto"),
        ("Warsaw", "Tallinn"),
        ("Santorini", "Milan"),
        ("Stockholm", "Prague"),
        ("Stockholm", "Tallinn"),
        ("Warsaw", "Milan"),
        ("Santorini", "Naples"),
        ("Warsaw", "Prague")
    }
    
    # Bidirectional flights
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    
    # Create a solver
    s = Solver()
    
    # Create variables: for each day (1 to 28) and each city, a boolean indicating if we are in that city on that day
    in_city = {}
    for city in cities:
        for day in range(1, 29):
            in_city[(city, day)] = Bool(f"in_{city}_{day}")
    
    # Constraint 1: For each city, the number of days we are in that city must be equal to the required days
    for city, days_req in cities.items():
        s.add(Sum([If(in_city[(city, day)], 1, 0) for day in range(1, 29)]) == days_req
    
    # Constraint 2: Fixed stays
    for city, start, end in fixed_stays:
        for day in range(start, end + 1):
            s.add(in_city[(city, day)])
    
    # Constraint 3: On each day, we are in at least one city and at most two cities
    for day in range(1, 29):
        in_cities = [in_city[(city, day)] for city in cities]
        s.add(Or(in_cities))  # At least one city
        s.add(Sum([If(v, 1, 0) for v in in_cities]) <= 2)
    
    # Constraint 4: If on a day we are in two cities, then there must be a direct flight between them
    for day in range(1, 29):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    # If we are in both city1 and city2 on this day, then there must be a flight
                    s.add(Implies(And(in_city[(city1, day)], in_city[(city2, day)]), 
                           Or((city1, city2) in bidirectional_flights, (city2, city1) in bidirectional_flights)))
    
    # Constraint 5: The entire trip is connected
    # We ensure that consecutive days are either the same city or adjacent via a direct flight
    for day in range(1, 28):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    # If we are in city1 on day and city2 on day+1, then we must be in both on day+1 (travel from city1 to city2 on day+1)
                    s.add(Implies(And(in_city[(city1, day)], in_city[(city2, day + 1)]),
                           And(in_city[(city1, day + 1)], in_city[(city2, day + 1)])))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Print the schedule
        schedule = {}
        for day in range(1, 29):
            for city in cities:
                if is_true(m.eval(in_city[(city, day)])):
                    if day not in schedule:
                        schedule[day] = []
                    schedule[day].append(city)
        # Output the schedule
        for day in sorted(schedule.keys()):
            cities_on_day = schedule[day]
            print(f"Day {day}: {', '.join(cities_on_day)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()