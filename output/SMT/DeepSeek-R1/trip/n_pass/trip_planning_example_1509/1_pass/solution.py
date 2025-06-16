from z3 import *

def main():
    # Define the City enum
    City = Datatype('City')
    cities_list = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    for c in cities_list:
        City.declare(c)
    City = City.create()
    Paris, Warsaw, Krakow, Tallinn, Riga, Copenhagen, Helsinki, Oslo, Santorini, Lyon = [getattr(City, c) for c in cities_list]
    
    # Map city names to their enum constants
    name_to_city = {c: getattr(City, c) for c in cities_list}
    
    # Define flight connections
    bidirectional_pairs = [
        ("Warsaw", "Riga"),
        ("Warsaw", "Tallinn"),
        ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"),
        ("Copenhagen", "Warsaw"),
        ("Lyon", "Oslo"),
        ("Paris", "Oslo"),
        ("Paris", "Riga"),
        ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"),
        ("Oslo", "Riga"),
        ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"),
        ("Copenhagen", "Santorini"),
        ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"),
        ("Copenhagen", "Krakow"),
        ("Copenhagen", "Riga"),
        ("Paris", "Krakow"),
        ("Copenhagen", "Oslo"),
        ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"),
        ("Copenhagen", "Tallinn"),
        ("Oslo", "Krakow"),
        ("Helsinki", "Tallinn"),
        ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"),
        ("Oslo", "Warsaw")
    ]
    
    unidirectional = [
        ("Riga", "Tallinn"),
        ("Santorini", "Oslo")
    ]
    
    allowed_flights = []
    for a_str, b_str in bidirectional_pairs:
        a_city = name_to_city[a_str]
        b_city = name_to_city[b_str]
        allowed_flights.append((a_city, b_city))
        allowed_flights.append((b_city, a_city))
    for a_str, b_str in unidirectional:
        a_city = name_to_city[a_str]
        b_city = name_to_city[b_str]
        allowed_flights.append((a_city, b_city))
    
    # Create base_city, travel, and dest arrays
    base_city = [None]  # index 0 unused
    for i in range(1, 27):
        base_city.append(Const(f'base_city_{i}', City))
    
    travel = [None]
    for i in range(1, 26):
        travel.append(Bool(f'travel_{i}'))
    
    dest = [None]
    for i in range(1, 26):
        dest.append(Const(f'dest_{i}', City))
    
    s = Solver()
    
    # Travel constraints
    for t in range(1, 26):
        s.add(Implies(travel[t], base_city[t] != dest[t]))
        options = []
        for a, b in allowed_flights:
            options.append(And(base_city[t] == a, dest[t] == b))
        s.add(Implies(travel[t], Or(options)))
        s.add(base_city[t+1] == If(travel[t], dest[t], base_city[t]))
    
    # Define in_city function
    def in_city(city, day):
        return Or(base_city[day] == city, And(travel[day], dest[day] == city))
    
    # Total days per city
    total_days = {
        Paris: 5,
        Warsaw: 2,
        Krakow: 2,
        Tallinn: 2,
        Riga: 2,
        Copenhagen: 5,
        Helsinki: 5,
        Oslo: 5,
        Santorini: 2,
        Lyon: 4
    }
    for city, days in total_days.items():
        s.add(Sum([If(in_city(city, t), 1, 0) for t in range(1, 26)]) == days)
    
    # Event constraints
    s.add(Or([in_city(Paris, t) for t in [4,5,6,7,8]]))
    s.add(Or(in_city(Krakow, 17), in_city(Krakow, 18))
    s.add(Or(in_city(Riga, 23), in_city(Riga, 24))
    s.add(Or([in_city(Helsinki, t) for t in range(18, 23)]))
    s.add(Or(in_city(Santorini, 12), in_city(Santorini, 13))
    
    # Exactly 9 travel days
    s.add(Sum([If(travel[t], 1, 0) for t in range(1, 26)]) == 9)
    
    # Check and output solution
    if s.check() == sat:
        m = s.model()
        for t in range(1, 26):
            base_val = m[base_city[t]]
            travel_val = m[travel[t]]
            if is_true(travel_val):
                dest_val = m[dest[t]]
                base_name = base_val.decl().name()
                dest_name = dest_val.decl().name()
                print(f"Day {t}: [{base_name}, {dest_name}]")
            else:
                base_name = base_val.decl().name()
                print(f"Day {t}: [{base_name}]")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()