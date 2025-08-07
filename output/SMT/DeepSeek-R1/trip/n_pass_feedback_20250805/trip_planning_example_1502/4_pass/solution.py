from z3 import *
import json

def main():
    # Cities and their durations
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
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Vienna", "Bucharest"),
        ("Santorini", "Madrid"),
        ("Seville", "Valencia"),
        ("Vienna", "Seville"),
        ("Madrid", "Valencia"),
        ("Bucharest", "Riga"),
        ("Valencia", "Bucharest"),
        ("Santorini", "Bucharest"),
        ("Vienna", "Valencia"),
        ("Vienna", "Madrid"),
        ("Valencia", "Krakow"),
        ("Valencia", "Frankfurt"),
        ("Krakow", "Frankfurt"),
        ("Riga", "Tallinn"),
        ("Vienna", "Krakow"),
        ("Vienna", "Frankfurt"),
        ("Madrid", "Seville"),
        ("Santorini", "Vienna"),
        ("Vienna", "Riga"),
        ("Frankfurt", "Tallinn"),
        ("Frankfurt", "Bucharest"),
        ("Madrid", "Bucharest"),
        ("Frankfurt", "Riga"),
        ("Madrid", "Frankfurt")
    ]
    # Make bidirectional
    direct_flights_set = set(direct_flights + [(b, a) for (a, b) in direct_flights])
    
    # Create solver
    s = Solver()
    
    # Create a Boolean variable for each city and each day
    in_city = {}
    for city in cities:
        for day in range(1, 28):
            in_city[(city, day)] = Bool(f"in_{city}_{day}")
    
    # Fixed city assignments
    fixed_assignments = {
        "Vienna": [3, 4, 5, 6],
        "Madrid": [6, 7],
        "Krakow": [11, 12, 13, 14, 15],
        "Riga": [20, 21, 22, 23],
        "Tallinn": [23, 24, 25, 26, 27]
    }
    for city, days_list in fixed_assignments.items():
        for day in range(1, 28):
            if day in days_list:
                s.add(in_city[(city, day)] == True)
            else:
                s.add(in_city[(city, day)] == False)
    
    # Constraints for specific travel days
    specific_travel_days = {
        3: ("Vienna", ["Santorini", "Valencia", "Seville", "Bucharest", "Frankfurt"]),
        6: ("Vienna", ["Madrid"]),
        7: ("Madrid", ["Santorini", "Valencia", "Seville", "Bucharest", "Frankfurt"]),
        11: ("Krakow", ["Valencia", "Frankfurt"]),
        15: ("Krakow", ["Valencia", "Frankfurt"]),
        20: ("Riga", ["Bucharest", "Frankfurt"]),
        23: ("Riga", ["Tallinn"])
    }
    for day, (fixed_city, other_cities) in specific_travel_days.items():
        # The fixed city is present
        s.add(in_city[(fixed_city, day)] == True)
        # Exactly one other city from the list is present
        if other_cities == ["Madrid"]:  # day6: only Vienna and Madrid
            s.add(in_city[("Madrid", day)] == True)
            for city in cities:
                if city != fixed_city and city != "Madrid":
                    s.add(in_city[(city, day)] == False)
        elif other_cities == ["Tallinn"]:  # day23: only Riga and Tallinn
            s.add(in_city[("Tallinn", day)] == True)
            for city in cities:
                if city != fixed_city and city != "Tallinn":
                    s.add(in_city[(city, day)] == False)
        else:
            other_vars = [in_city[(other, day)] for other in other_cities]
            # Exactly one of the other cities is present
            s.add(AtLeast(*other_vars, 1))
            s.add(AtMost(*other_vars, 1))
            # For cities not in the list, they are not present on this day
            for city in cities:
                if city != fixed_city and city not in other_cities:
                    s.add(in_city[(city, day)] == False)
    
    # Duration constraints for non-fixed cities
    non_fixed_cities = ["Santorini", "Valencia", "Seville", "Bucharest", "Frankfurt"]
    for city in non_fixed_cities:
        total_days = durations[city]
        s.add(Sum([If(in_city[(city, day)], 1, 0) for day in range(1, 28)]) == total_days)
    
    # For each day, at least one city and at most two cities
    for day in range(1, 28):
        vars_day = [in_city[(city, day)] for city in cities]
        s.add(AtLeast(*vars_day, 1))
        s.add(AtMost(*vars_day, 2))
    
    # If two cities on a day, they must have a direct flight
    for day in range(1, 28):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                both_present = And(in_city[(city_i, day)], in_city[(city_j, day)])
                flight_exists = (city_i, city_j) in direct_flights_set
                s.add(Implies(both_present, flight_exists))
    
    # Continuity constraints
    for city in cities:
        for day in range(1, 27):
            # If present on day and not on day+1, then there must be a flight out on day
            in_day = in_city[(city, day)]
            in_next = in_city[(city, day+1)]
            leave = And(in_day, Not(in_next))
            # There exists another city B such that on day, both city and B are present and they have a flight
            other_cities = [other for other in cities if other != city]
            options = []
            for other in other_cities:
                flight_ok = (city, other) in direct_flights_set
                options.append(And(in_city[(other, day)], flight_ok))
            s.add(Implies(leave, Or(options)))
            
            # If not present on day and present on day+1, then there must be a flight in on day+1
            arrive = And(Not(in_day), in_next)
            options_arrive = []
            for other in other_cities:
                flight_ok = (city, other) in direct_flights_set
                options_arrive.append(And(in_city[(other, day+1)], flight_ok))
            s.add(Implies(arrive, Or(options_arrive)))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 28):
            cities_today = []
            for city in cities:
                if is_true(model[in_city[(city, day)]]):
                    cities_today.append(city)
            itinerary.append({"day": day, "cities": cities_today})
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()