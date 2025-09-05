from z3 import *
import json

def main():
    s = Solver()

    # Define cities and their required durations
    cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
    durations = {
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
    # Mapping from city name to index
    city_to_idx = {city: i for i, city in enumerate(cities)}

    # Build allowed flight connections.
    # For undirected connections, we add both directions;
    # For directed ones, only the specified direction is allowed.
    allowed_flights = []
    def add_undirected(a, b):
        allowed_flights.append((city_to_idx[a], city_to_idx[b]))
        allowed_flights.append((city_to_idx[b], city_to_idx[a]))
    def add_directed(a, b):
        allowed_flights.append((city_to_idx[a], city_to_idx[b]))

    add_undirected("Riga", "Prague")          # Riga and Prague
    add_undirected("Stockholm", "Milan")        # Stockholm and Milan
    add_undirected("Riga", "Milan")             # Riga and Milan
    add_undirected("Lisbon", "Stockholm")       # Lisbon and Stockholm
    add_directed("Stockholm", "Santorini")       # from Stockholm to Santorini
    add_undirected("Naples", "Warsaw")          # Naples and Warsaw
    add_undirected("Lisbon", "Warsaw")          # Lisbon and Warsaw
    add_undirected("Naples", "Milan")           # Naples and Milan
    add_undirected("Lisbon", "Naples")          # Lisbon and Naples
    add_directed("Riga", "Tallinn")             # from Riga to Tallinn
    add_undirected("Tallinn", "Prague")         # Tallinn and Prague
    add_undirected("Stockholm", "Warsaw")       # Stockholm and Warsaw
    add_undirected("Riga", "Warsaw")            # Riga and Warsaw
    add_undirected("Lisbon", "Riga")            # Lisbon and Riga
    add_undirected("Riga", "Stockholm")         # Riga and Stockholm
    add_undirected("Lisbon", "Porto")           # Lisbon and Porto
    add_undirected("Lisbon", "Prague")          # Lisbon and Prague
    add_undirected("Milan", "Porto")            # Milan and Porto
    add_undirected("Prague", "Milan")           # Prague and Milan
    add_undirected("Lisbon", "Milan")           # Lisbon and Milan
    add_undirected("Warsaw", "Porto")           # Warsaw and Porto
    add_undirected("Warsaw", "Tallinn")         # Warsaw and Tallinn
    add_undirected("Santorini", "Milan")        # Santorini and Milan
    add_undirected("Stockholm", "Prague")       # Stockholm and Prague
    add_undirected("Stockholm", "Tallinn")      # Stockholm and Tallinn
    add_undirected("Warsaw", "Milan")           # Warsaw and Milan
    add_undirected("Santorini", "Naples")       # Santorini and Naples
    add_undirected("Warsaw", "Prague")          # Warsaw and Prague

    # Remove duplicate connections if any
    allowed_flights = list(set(allowed_flights))

    # Create variables for the itinerary segments.
    # "order" holds the sequence of cities (each as an integer index).
    order = [Int(f"order_{i}") for i in range(10)]
    for o in order:
        s.add(And(o >= 0, o < 10))
    s.add(Distinct(order))

    # Define start and end day for each segment.
    start_days = [Int(f"start_{i}") for i in range(10)]
    end_days = [Int(f"end_{i}") for i in range(10)]
    
    # The trip starts on Day 1 and must finish on Day 28.
    s.add(start_days[0] == 1)
    s.add(end_days[9] == 28)

    # For each segment, set the end day based on the required duration of the visited city.
    for i in range(10):
        # For each possible city, if the segment chooses that city,
        # then its duration is fixed: end = start + (duration - 1).
        conds = []
        for city in cities:
            dur = durations[city]
            conds.append(If(order[i] == city_to_idx[city],
                            end_days[i] == start_days[i] + dur - 1,
                            True))
        s.add(And(conds))
        
        # Additional time constraints for specific events:
        # In Tallinn, visit relatives between Day 18 and Day 20.
        s.add(Implies(order[i] == city_to_idx["Tallinn"],
                      And(start_days[i] <= 20, end_days[i] >= 18)))
        # In Milan, meet a friend between Day 24 and Day 26.
        s.add(Implies(order[i] == city_to_idx["Milan"],
                      And(start_days[i] <= 26, end_days[i] >= 24)))
        # In Riga, attend the annual show from Day 5 to Day 8.
        s.add(Implies(order[i] == city_to_idx["Riga"],
                      And(start_days[i] <= 5, end_days[i] >= 8)))
    
    # Consecutive segments share a flight day (the end of one is the start of the next).
    for i in range(1, 10):
        s.add(start_days[i] == end_days[i-1])

    # Constrain flight connections between consecutive cities.
    for i in range(9):
        possible = []
        for (a, b) in allowed_flights:
            possible.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(possible))

    # Check if a valid itinerary exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(10):
            city_index = m.evaluate(order[i]).as_long()
            city_name = cities[city_index]
            s_day = m.evaluate(start_days[i]).as_long()
            e_day = m.evaluate(end_days[i]).as_long()
            itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": city_name})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()