from z3 import *

def main():
    # Define the City enumeration
    City, cities = EnumSort('City', ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split'])
    Hamburg, Munich, Manchester, Lyon, Split = cities

    # Create a mapping for city names for output
    city_names = {
        Hamburg: "Hamburg",
        Munich: "Munich",
        Manchester: "Manchester",
        Lyon: "Lyon",
        Split: "Split"
    }

    # Define the directed flights set
    directed_flights = set()

    # Define undirected edges as string pairs
    undirected_edges = [
        ('Split', 'Munich'),
        ('Munich', 'Manchester'),
        ('Hamburg', 'Manchester'),
        ('Hamburg', 'Munich'),
        ('Split', 'Lyon'),
        ('Lyon', 'Munich'),
        ('Hamburg', 'Split')
    ]
    
    # Map string names to Z3 constants
    str_to_city = {
        'Hamburg': Hamburg,
        'Munich': Munich,
        'Manchester': Manchester,
        'Lyon': Lyon,
        'Split': Split
    }

    # Add bidirectional edges for undirected flights
    for a, b in undirected_edges:
        c1 = str_to_city[a]
        c2 = str_to_city[b]
        directed_flights.add((c1, c2))
        directed_flights.add((c2, c1))
    
    # Add directed flight from Manchester to Split
    directed_flights.add((Manchester, Split))

    # Create start and end variables for 20 days (index 0 to 19 for days 1 to 20)
    start = [Const('start_%d' % i, City) for i in range(1, 21)]
    end = [Const('end_%d' % i, City) for i in range(1, 21)]

    s = Solver()

    # Constraint 1: Chain constraint (end of day i must equal start of day i+1)
    for i in range(0, 19):
        s.add(end[i] == start[i+1])

    # Constraint 2: Flight constraints
    for i in range(0, 20):
        # If a flight is taken on day i, the flight must be in the directed_flights set
        flight_taken = (start[i] != end[i])
        valid_flight = Or([And(start[i] == c1, end[i] == c2) for (c1, c2) in directed_flights])
        s.add(If(flight_taken, valid_flight, True))

    # Constraint 3: Specific day constraints
    # Must be in Lyon at the end of day 13 (index 12) for the show
    s.add(end[12] == Lyon)
    # Must be in Manchester at the end of day 19 (index 18) for relatives
    s.add(end[18] == Manchester)

    # Constraint 4: Total days per city
    required_days = {
        Hamburg: 7,
        Munich: 6,
        Manchester: 2,
        Lyon: 2,
        Split: 7
    }

    for city, days_req in required_days.items():
        total = 0
        for i in range(0, 20):
            # Count day if: start[i] is the city OR (end[i] is the city and start[i] is not the city)
            cond = Or(start[i] == city, And(end[i] == city, start[i] != city))
            total += If(cond, 1, 0)
        s.add(total == days_req)

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(0, 20):
            day = i + 1
            s_val = model.eval(start[i])
            e_val = model.eval(end[i])
            s_name = city_names[s_val]
            e_name = city_names[e_val]
            if s_name == e_name:
                cities_of_day = [s_name]
            else:
                cities_of_day = [s_name, e_name]
            itinerary.append({"day": day, "city": cities_of_day})
        
        # Output the itinerary in JSON format
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()