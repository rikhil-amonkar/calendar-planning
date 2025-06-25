from z3 import *

def main():
    # City mapping
    city_const_to_name = {
        'CITY1': 'Paris',
        'CITY2': 'Brussels',
        'CITY3': 'Berlin',
        'CITY4': 'Vienna',
        'CITY5': 'Prague',
        'CITY6': 'Rome',
        'CITY7': 'Madrid',
        'CITY8': 'Barcelona',
        'CITY9': 'London'
    }
    
    # Reverse mapping
    name_to_city_const = {v: k for k, v in city_const_to_name.items()}
    
    # Travel edges and days
    travel_edges = [
        ('Paris', 'Brussels'), ('Paris', 'London'), ('Paris', 'Barcelona'), 
        ('Brussels', 'Berlin'), ('Brussels', 'London'), 
        ('Berlin', 'Vienna'), ('Berlin', 'Prague'), 
        ('Vienna', 'Prague'), ('Vienna', 'Rome'), 
        ('Prague', 'Rome'), ('Prague', 'Barcelona'), 
        ('Rome', 'Barcelona'), ('Rome', 'Madrid'), 
        ('Madrid', 'Barcelona'), ('Madrid', 'London'), 
        ('Barcelona', 'London'), ('London', 'Barcelona')
    ]
    
    travel_days = {
        ('Paris', 'Brussels'): 2,
        ('Paris', 'London'): 4,
        ('Paris', 'Barcelona'): 3,
        ('Brussels', 'Berlin'): 3,
        ('Brussels', 'London'): 4,
        ('Berlin', 'Vienna'): 4,
        ('Berlin', 'Prague'): 2,
        ('Vienna', 'Prague'): 1,
        ('Vienna', 'Rome'): 3,
        ('Prague', 'Rome'): 4,
        ('Prague', 'Barcelona'): 5,
        ('Rome', 'Barcelona'): 2,
        ('Rome', 'Madrid'): 3,
        ('Madrid', 'Barcelona'): 2,
        ('Madrid', 'London'): 5,
        ('Barcelona', 'London'): 3,
        ('London', 'Barcelona'): 3
    }
    
    # Stay durations
    duration_dict = {
        'CITY1': 3,   # Paris
        'CITY2': 2,   # Brussels
        'CITY3': 4,   # Berlin
        'CITY4': 3,   # Vienna
        'CITY5': 2,   # Prague
        'CITY6': 4,   # Rome
        'CITY7': 3,   # Madrid
        'CITY8': 2,   # Barcelona
        'CITY9': 5    # London
    }
    
    # Setup
    available_days = 24
    city_names = ['Paris', 'Brussels', 'Berlin', 'Vienna', 'Prague', 'Rome', 'Madrid', 'Barcelona', 'London']
    start_city = 'Paris'
    end_city = 'London'
    total_days = available_days
    
    # Create City enumeration type
    CitySort, city_consts = EnumSort('City', city_names)
    name_to_z3const = {name: const for name, const in zip(city_names, city_consts)}
    z3const_to_name = {const: name for name, const in name_to_z3const.items()}
    
    # Initialize solver
    s = Solver()
    
    # Declare functions
    Arrival = Function('Arrival', CitySort, IntSort())
    Departure = Function('Departure', CitySort, IntSort())
    Visited = Function('Visited', CitySort, BoolSort())
    
    # Get Z3 constants for start/end cities
    start_z3 = name_to_z3const[start_city]
    end_z3 = name_to_z3const[end_city]
    
    # Must visit start and end cities
    s.add(Visited(start_z3))
    s.add(Visited(end_z3))
    
    # Start/end constraints
    s.add(Arrival(start_z3) == 1)
    s.add(Departure(end_z3) == total_days)
    
    # City constraints
    for city_name in city_names:
        c = name_to_z3const[city_name]
        const_name = name_to_city_const[city_name]
        d = duration_dict[const_name]
        
        # Only constrain visited cities
        s.add(Implies(Visited(c), Arrival(c) >= 1))
        s.add(Implies(Visited(c), Departure(c) >= 1))
        s.add(Implies(Visited(c), Departure(c) >= Arrival(c)))
        s.add(Implies(Visited(c), Departure(c) - Arrival(c) >= d))
    
    # Travel constraints between visited cities
    for edge in travel_edges:
        city1, city2 = edge
        c1 = name_to_z3const[city1]
        c2 = name_to_z3const[city2]
        travel_time = travel_days[edge]
        
        s.add(Implies(And(Visited(c1), Visited(c2)),
                     Arrival(c2) >= Departure(c1) + travel_time))
    
    # Total trip duration
    s.add(Departure(end_z3) - Arrival(start_z3) <= available_days)
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        for z3_const in city_consts:
            city_name = z3const_to_name[z3_const]
            if is_true(m.evaluate(Visited(z3_const))):
                arrive = m.evaluate(Arrival(z3_const))
                depart = m.evaluate(Departure(z3_const))
                print(f"{city_name}: Arrive on day {arrive}, Depart on day {depart}")
            else:
                print(f"{city_name}: Not visited")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()