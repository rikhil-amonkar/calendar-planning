import z3
import json

def main():
    # Define the City enum
    City, (Riga, Frankfurt, Amsterdam, Vilnius, London, Stockholm, Bucharest) = z3.EnumSort('City', 
        ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest'])
    
    # Map for city names
    name_map = {
        Riga: "Riga",
        Frankfurt: "Frankfurt",
        Amsterdam: "Amsterdam",
        Vilnius: "Vilnius",
        London: "London",
        Stockholm: "Stockholm",
        Bucharest: "Bucharest"
    }
    
    # Required days per city
    required_days = {
        Riga: 2,
        Frankfurt: 3,
        Amsterdam: 2,
        Vilnius: 5,
        London: 2,
        Stockholm: 3,
        Bucharest: 4
    }
    
    # Build the list of allowed flights (directed edges)
    allowed_flights = []
    bidirectional_edges = [
        ('London', 'Amsterdam'),
        ('Vilnius', 'Frankfurt'),
        ('Riga', 'Stockholm'),
        ('London', 'Bucharest'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Frankfurt'),
        ('Frankfurt', 'Stockholm'),
        ('Bucharest', 'Riga'),
        ('Amsterdam', 'Riga'),
        ('Amsterdam', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Bucharest', 'Frankfurt'),
        ('London', 'Frankfurt'),
        ('London', 'Stockholm'),
        ('Amsterdam', 'Vilnius')
    ]
    
    # Add bidirectional flights (both directions)
    for a, b in bidirectional_edges:
        a_const = globals()[a]
        b_const = globals()[b]
        allowed_flights.append((a_const, b_const))
        allowed_flights.append((b_const, a_const))
    
    # Add directed flight: Riga to Vilnius
    allowed_flights.append((Riga, Vilnius))
    
    # Create Z3 variables for s and e arrays (15 days)
    s = [z3.Const(f's_{i}', City) for i in range(15)]  # start city for each day
    e = [z3.Const(f'e_{i}', City) for i in range(15)]  # end city for each day
    
    solver = z3.Solver()
    
    # Constraint: The end city of day i must be the start city of day i+1
    for i in range(14):
        solver.add(e[i] == s[i+1])
    
    # Constraint: For each day, if start and end cities differ, there must be a direct flight
    for i in range(15):
        same_city = s[i] == e[i]
        flight_options = []
        for (u, v) in allowed_flights:
            flight_options.append(z3.And(s[i] == u, e[i] == v))
        solver.add(z3.Or(same_city, z3.Or(flight_options)))
    
    # Total days per city constraint
    for city in [Riga, Frankfurt, Amsterdam, Vilnius, London, Stockholm, Bucharest]:
        total = 0
        for i in range(15):
            total += z3.If(z3.Or(s[i] == city, e[i] == city), 1, 0)
        solver.add(total == required_days[city])
    
    # Event constraints
    # Amsterdam: must be present on day 2 or 3
    ams_day2 = z3.Or(s[1] == Amsterdam, e[1] == Amsterdam)  # day2: index1
    ams_day3 = z3.Or(s[2] == Amsterdam, e[2] == Amsterdam)  # day3: index2
    solver.add(z3.Or(ams_day2, ams_day3))
    
    # Vilnius: must be present between day7 (index6) and day11 (index10)
    vilnius_days = []
    for i in [6,7,8,9,10]:
        vilnius_days.append(z3.Or(s[i] == Vilnius, e[i] == Vilnius))
    solver.add(z3.Or(vilnius_days))
    
    # Stockholm: must be present between day13 (index12) and day15 (index14)
    stockholm_days = []
    for i in [12,13,14]:
        stockholm_days.append(z3.Or(s[i] == Stockholm, e[i] == Stockholm))
    solver.add(z3.Or(stockholm_days))
    
    # Check for a solution
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary_list = []
        for i in range(15):
            day = i + 1
            s_val = model.eval(s[i])
            e_val = model.eval(e[i])
            s_name = name_map[s_val]
            e_name = name_map[e_val]
            if s_val == e_val:
                places = [s_name]
            else:
                places = [s_name, e_name]
            itinerary_list.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()