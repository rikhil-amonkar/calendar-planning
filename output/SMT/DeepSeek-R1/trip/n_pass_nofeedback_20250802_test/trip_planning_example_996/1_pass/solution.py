from z3 import *

def main():
    # Define the cities
    cities = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
    City = Datatype('City')
    for c in cities:
        City.declare(c)
    City = City.create()
    valencia, riga, prague, mykonos, zurich, bucharest, nice = [getattr(City, c) for c in cities]

    # Required days per city
    req_days = {
        valencia: 5,
        riga: 5,
        prague: 3,
        mykonos: 3,
        zurich: 5,
        bucharest: 5,
        nice: 2
    }

    # Direct flights (undirected graph, stored as bidirectional edges)
    edges_list = [
        ('Mykonos', 'Nice'),
        ('Mykonos', 'Zurich'),
        ('Prague', 'Bucharest'),
        ('Valencia', 'Bucharest'),
        ('Zurich', 'Prague'),
        ('Riga', 'Nice'),
        ('Zurich', 'Riga'),
        ('Zurich', 'Bucharest'),
        ('Zurich', 'Valencia'),
        ('Bucharest', 'Riga'),
        ('Prague', 'Riga'),
        ('Prague', 'Valencia'),
        ('Zurich', 'Nice')
    ]
    
    # Create a set of directed edges (both directions)
    allowed_edges = set()
    for a, b in edges_list:
        a_const = getattr(City, a)
        b_const = getattr(City, b)
        allowed_edges.add((a_const, b_const))
        allowed_edges.add((b_const, a_const))

    # Create 23 variables: x0 (start of day1), x1 (end of day1), ..., x22 (end of day22)
    x = [Const(f'x{i}', City) for i in range(23)]
    
    s = Solver()
    
    # Constraint 1: Flight connections for consecutive days
    for i in range(1, 23):
        s.add(If(
            x[i-1] != x[i],
            Or([And(x[i-1] == a, x[i] == b) for (a, b) in allowed_edges]),
            True
        ))
    
    # Constraint 2: Total days per city
    for city in [valencia, riga, prague, mykonos, zurich, bucharest, nice]:
        part1 = Sum([If(x[i] == city, 1, 0) for i in range(0, 22)])  # x0 to x21
        part2_list = []
        for i in range(1, 23):
            cond = And(x[i] == city, x[i-1] != city)
            part2_list.append(If(cond, 1, 0))
        part2 = Sum(part2_list)
        total_days = part1 + part2
        s.add(total_days == req_days[city])
    
    # Constraint 3: Event constraints
    # Mykonos must be visited on at least one day between 1 and 3 (inclusive)
    s.add(Or([x[i] == mykonos for i in range(0, 4)]))  # x0, x1, x2, x3
    # Prague must be visited on at least one day between 7 and 9 (inclusive)
    s.add(Or([x[i] == prague for i in range(6, 10)]))  # x6, x7, x8, x9

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        city_names = {
            valencia: "Valencia",
            riga: "Riga",
            prague: "Prague",
            mykonos: "Mykonos",
            zurich: "Zurich",
            bucharest: "Bucharest",
            nice: "Nice"
        }
        itinerary = []
        # For day 1 to 22, the place is the end-of-day city (x1 to x22)
        for day in range(1, 23):
            idx = day  # x[day] is the end of day `day`
            city_val = m[x[idx]]
            city_str = city_names[city_val]
            itinerary.append({"day": day, "place": city_str})
        result = {"itinerary": itinerary}
        # Output the result in JSON format
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()