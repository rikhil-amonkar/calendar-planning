from z3 import *
import json

def main():
    # Define city names and durations
    cities = ["Santorini", "Valencia", "Madrid", "Seville", "Bucharest", "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"]
    durations = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }
    
    # Event constraints: city -> list of days that must be included
    events = {
        "Vienna": [3, 4, 5, 6],
        "Madrid": [6, 7],
        "Riga": [20, 21, 22, 23],
        "Tallinn": [23, 24, 25, 26, 27],
        "Krakow": [11, 12, 13, 14, 15]
    }
    
    # Direct flights as a set of tuples (city1, city2)
    direct_flights = {
        ("Vienna", "Bucharest"), ("Santorini", "Madrid"), ("Seville", "Valencia"), ("Vienna", "Seville"),
        ("Madrid", "Valencia"), ("Bucharest", "Riga"), ("Valencia", "Bucharest"), ("Santorini", "Bucharest"),
        ("Vienna", "Valencia"), ("Vienna", "Madrid"), ("Valencia", "Krakow"), ("Valencia", "Frankfurt"),
        ("Krakow", "Frankfurt"), ("Riga", "Tallinn"), ("Vienna", "Krakow"), ("Vienna", "Frankfurt"),
        ("Madrid", "Seville"), ("Santorini", "Vienna"), ("Vienna", "Riga"), ("Frankfurt", "Tallinn"),
        ("Frankfurt", "Bucharest"), ("Madrid", "Bucharest"), ("Frankfurt", "Riga"), ("Madrid", "Frankfurt")
    }
    # Ensure flight pairs are bidirectional
    direct_flights.update({(b, a) for (a, b) in direct_flights})
    
    # Create a Z3 solver
    s = Solver()
    
    # Create a Boolean variable for each city and each day (1 to 27)
    in_city = {}
    for city in cities:
        for day in range(1, 28):
            in_city[(city, day)] = Bool(f"in_{city}_{day}")
    
    # Constraint 1: For each day, at least one city and at most two cities
    for day in range(1, 28):
        cities_on_day = [in_city[(city, day)] for city in cities]
        s.add(AtLeast(*cities_on_day, 1))
        s.add(AtMost(*cities_on_day, 2))
        
        # If two cities on a day, they must have a direct flight
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                # If both are present, then there must be a flight
                both_present = And(in_city[(city_i, day)], in_city[(city_j, day)])
                s.add(Implies(both_present, Or(
                    (city_i, city_j) in direct_flights,
                    (city_j, city_i) in direct_flights
                )))
    
    # Constraint 2: Duration constraints
    for city in cities:
        total_days = durations[city]
        s.add(Sum([If(in_city[(city, day)], 1, 0) for day in range(1, 28)]) == total_days)
    
    # Constraint 3: Event constraints
    for city, event_days in events.items():
        for day in event_days:
            s.add(in_city[(city, day)])
    
    # Constraint 4: Consecutive days constraint
    for day in range(1, 27):
        for city in cities:
            # If in the city on day+1, then either in the city on day or flew from another city on day
            next_day_in = in_city[(city, day+1)]
            # If we are in 'city' on day+1, then on day we must be either in 'city' or in some other city that has a direct flight to 'city'
            # and also we must be in 'city' on day (because flight lands on day)
            options = [in_city[(city, day)]]  # staying in the same city
            for other in cities:
                if other != city and ((other, city) in direct_flights or (city, other) in direct_flights):
                    options.append(And(in_city[(other, day)], in_city[(city, day)]))
            s.add(Implies(next_day_in, Or(options)))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 28):
            cities_today = []
            for city in cities:
                if is_true(model[in_city[(city, day)]]):
                    cities_today.append(city)
            itinerary.append({"day": day, "cities": cities_today})
        
        # Format the output as JSON
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()