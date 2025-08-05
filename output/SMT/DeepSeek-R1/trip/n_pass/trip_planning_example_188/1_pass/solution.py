from z3 import *
import json

def main():
    # Define symbolic constants for cities
    CitySort = Datatype('CitySort')
    CitySort.declare('Brussels')
    CitySort.declare('Barcelona')
    CitySort.declare('Split')
    CitySort = CitySort.create()
    brussels = CitySort.Brussels
    barcelona = CitySort.Barcelona
    split = CitySort.Split

    # Map symbolic constants to string names
    city_map = {
        brussels: 'Brussels',
        barcelona: 'Barcelona',
        split: 'Split'
    }
    
    s_sym = [None] * 13
    s_sym[0] = brussels  # Start at Brussels at the beginning of day 1
    
    # Create Z3 variables for s[1] to s[12] (sleeping cities at the end of each day)
    for i in range(1, 13):
        s_sym[i] = Const(f's{i}', CitySort)
    
    solver = Solver()
    
    # Define direct flight pairs
    direct_flights = [
        (brussels, barcelona),
        (barcelona, brussels),
        (barcelona, split),
        (split, barcelona)
    ]
    
    # Flight constraints: if moving between cities, ensure direct flight exists
    for i in range(1, 13):
        flight = (s_sym[i] != s_sym[i-1])
        allowed_flight = Or([And(s_sym[i-1] == dep, s_sym[i] == arr) for dep, arr in direct_flights])
        solver.add(Implies(flight, allowed_flight))
    
    # Define presence in each city for each day
    in_brussels = [None] * 12  # For days 1 to 12
    in_barcelona = [None] * 12
    in_split = [None] * 12
    
    for i in range(1, 13):  # Day i (1 to 12)
        flight_day = (s_sym[i] != s_sym[i-1])
        idx = i - 1  # Index in presence arrays (0 to 11)
        
        # Presence in Brussels on day i
        in_brussels[idx] = Or(
            And(Not(flight_day), s_sym[i] == brussels),
            And(flight_day, Or(s_sym[i-1] == brussels, s_sym[i] == brussels))
        )
        # Presence in Barcelona on day i
        in_barcelona[idx] = Or(
            And(Not(flight_day), s_sym[i] == barcelona),
            And(flight_day, Or(s_sym[i-1] == barcelona, s_sym[i] == barcelona))
        )
        # Presence in Split on day i
        in_split[idx] = Or(
            And(Not(flight_day), s_sym[i] == split),
            And(flight_day, Or(s_sym[i-1] == split, s_sym[i] == split))
        )
    
    # Total days per city constraints
    total_brussels = Sum([If(in_brussels[i], 1, 0) for i in range(12)])
    total_barcelona = Sum([If(in_barcelona[i], 1, 0) for i in range(12)])
    total_split = Sum([If(in_split[i], 1, 0) for i in range(12)])
    
    solver.add(total_brussels == 2)
    solver.add(total_barcelona == 7)
    solver.add(total_split == 5)
    
    # Brussels must be present on days 1 and 2 (conference constraint)
    solver.add(in_brussels[0] == True)  # Day 1
    solver.add(in_brussels[1] == True)  # Day 2
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        # Get the sleeping city for each day
        sleeping_cities = [None] * 13
        sleeping_cities[0] = brussels
        for i in range(1, 13):
            sleeping_cities[i] = m.eval(s_sym[i])
        
        # Build itinerary: days 1 and 2 are Brussels, days 3-12 use the sleeping city
        itinerary = []
        for day in range(1, 13):
            if day <= 2:
                place = 'Brussels'
            else:
                sym_city = sleeping_cities[day]  # Sleeping city at end of day
                place = city_map[sym_city]
            itinerary.append({"day": day, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()