from z3 import *

def main():
    # Define the city mapping
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
    
    # Create reverse mapping
    name_to_city_const = {v: k for k, v in city_const_to_name.items()}
    
    # Define the travel_edges and travel_days
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
    
    # Define the duration of stay in each city
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
    
    # Available days and cities
    available_days = 30
    city_names = ['Paris', 'Brussels', 'Berlin', 'Vienna', 'Prague', 'Rome', 'Madrid', 'Barcelona', 'London']
    start_city = 'Paris'
    end_city = 'London'
    total_days = available_days
    
    # Create City enumeration type
    CitySort, city_consts = EnumSort('City', city_names)
    # Create a mapping from city name to Z3 constant
    name_to_z3const = {name: const for name, const in zip(city_names, city_consts)}
    # Create a mapping from Z3 constant to city name
    z3const_to_name = {const: name for name, const in name_to_z3const.items()}
    
    # Initialize Z3 solver and functions
    s = Solver()
    
    # Arrival and departure functions for each city
    Arrival = Function('Arrival', CitySort, IntSort())
    Departure = Function('Departure', CitySort, IntSort())
    
    # Constraint: Arrival and departure for each city
    for city_name in city_names:
        c = name_to_z3const[city_name]
        s.add(Arrival(c) >= 1)
        s.add(Departure(c) >= 1)
        s.add(Departure(c) >= Arrival(c))
    
    # Constraint: Start and end conditions
    s.add(Arrival(name_to_z3const[start_city]) == 1)
    s.add(Departure(name_to_z3const[end_city]) == total_days)
    
    # Constraint: At least the specified number of days in each city
    for city_name in city_names:
        c = name_to_z3const[city_name]
        const_name = name_to_city_const[city_name]
        d = duration_dict[const_name]
        s.add(Departure(c) - Arrival(c) >= d)
    
    # Constraint: Travel edges
    for edge in travel_edges:
        city1, city2 = edge
        c1 = name_to_z3const[city1]
        c2 = name_to_z3const[city2]
        s.add(Departure(c1) < Arrival(c2))
    
    # Constraint: Total trip duration
    s.add(Departure(name_to_z3const[end_city]) - Arrival(name_to_z3const[start_city]) <= available_days)
    
    # Check and print the solution
    if s.check() == sat:
        m = s.model()
        for z3_const in city_consts:
            city_name = z3const_to_name[z3_const]
            arrive = m.evaluate(Arrival(z3_const))
            depart = m.evaluate(Departure(z3_const))
            print(f"{city_name}: Arrive on day {arrive}, Depart on day {depart}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()