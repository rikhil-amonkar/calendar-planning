from z3 import *

def main():
    # Define the City enumeration
    City, (Hamburg, Munich, Manchester, Lyon, Split) = EnumSort('City', ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split'])
    city_names = {
        Hamburg: "Hamburg",
        Munich: "Munich",
        Manchester: "Manchester",
        Lyon: "Lyon",
        Split: "Split"
    }

    # Define the directed flights set
    directed_flights = set()

    undirected_edges = [
        ('Split', 'Munich'),
        ('Munich', 'Manchester'),
        ('Hamburg', 'Manchester'),
        ('Hamburg', 'Munich'),
        ('Split', 'Lyon'),
        ('Lyon', 'Munich'),
        ('Hamburg', 'Split')
    ]

    # Add bidirectional edges for undirected flights
    for a, b in undirected_edges:
        c1 = City[a]
        c2 = City[b]
        directed_flights.add((c1, c2))
        directed_flights.add((c2, c1))

    # Add directed flight from Manchester to Split
    directed_flights.add((City['Manchester'], City['Split']))

    # Create start and end variables for 20 days
    start = [Const('start_%d' % i, City) for i in range(1, 21)]
    end = [Const('end_%d' % i, City) for i in range(1, 21)]

    s = Solver()

    # Constraint 1: Chain constraint (end of day i must equal start of day i+1)
    for i in range(0, 19):
        s.add(end[i] == start[i+1])

    # Constraint 2: Flight constraints
    for i in range(0, 20):
        # If start[i] != end[i], then (start[i], end[i]) must be in directed_flights
        flight_taken = (start[i] != end[i])
        valid_flight = Or([And(start[i] == c1, end[i] == c2) for (c1, c2) in directed_flights])
        s.add(If(flight_taken, valid_flight, True))

    # Constraint 3: Specific day constraints
    s.add(end[12] == Lyon)   # End of day 13 (index 12) must be Lyon
    s.add(end[18] == Manchester)  # End of day 19 (index 18) must be Manchester

    # Constraint 4: Total days per city
    required_days = {
        Hamburg: 7,
        Munich: 6,
        Manchester: 2,
        Lyon: 2,
        Split: 7
    }

    for city in [Hamburg, Munich, Manchester, Lyon, Split]:
        total = 0
        for i in range(0, 20):
            # Count day if: start[i] == city OR (end[i] == city and start[i] != city)
            cond = Or(start[i] == city, And(end[i] == city, start[i] != city))
            total += If(cond, 1, 0)
        s.add(total == required_days[city])

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
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()