from z3 import *

def main():
    # Define the City datatype
    City = Datatype('City')
    City.declare('Dublin')
    City.declare('Reykjavik')
    City.declare('London')
    City.declare('Mykonos')
    City.declare('Hamburg')
    City.declare('Helsinki')
    City = City.create()
    
    # Create solver
    s = Solver()
    
    # Define variables for start and end of each day (days 1 to 16, indexed 0 to 15)
    start = [Const('start_%d' % i, City) for i in range(16)]
    end = [Const('end_%d' % i, City) for i in range(16)]
    
    # Continuity constraint: end of day i must be start of day i+1
    for i in range(15):
        s.add(end[i] == start[i+1])
    
    # Define direct flight edges (both directions)
    edges = [
        (City.Dublin, City.London),
        (City.Hamburg, City.Dublin),
        (City.Helsinki, City.Reykjavik),
        (City.Hamburg, City.London),
        (City.Dublin, City.Helsinki),
        (City.Reykjavik, City.London),
        (City.London, City.Mykonos),
        (City.Dublin, City.Reykjavik),
        (City.Hamburg, City.Helsinki),
        (City.Helsinki, City.London)
    ]
    directed_flights = []
    for a, b in edges:
        directed_flights.append((a, b))
        directed_flights.append((b, a))
    
    # Flight constraints: if start and end differ, must be a direct flight
    for i in range(16):
        flight_ok = Or([And(start[i] == a, end[i] == b) for a, b in directed_flights])
        s.add(If(start[i] != end[i], flight_ok, True))
    
    # Total days per city
    cities = [City.Dublin, City.Reykjavik, City.London, City.Mykonos, City.Hamburg, City.Helsinki]
    total_days = {c: 0 for c in cities}
    for c in cities:
        for i in range(16):
            total_days[c] += If(Or(start[i] == c, end[i] == c), 1, 0)
    
    s.add(total_days[City.Dublin] == 5)
    s.add(total_days[City.Reykjavik] == 2)
    s.add(total_days[City.London] == 5)
    s.add(total_days[City.Mykonos] == 3)
    s.add(total_days[City.Hamburg] == 2)
    s.add(total_days[City.Helsinki] == 4)
    
    # Event constraints
    # Hamburg: must be in Hamburg on day 1 or 2
    s.add(Or(Or(start[0] == City.Hamburg, end[0] == City.Hamburg),
             Or(start[1] == City.Hamburg, end[1] == City.Hamburg)))
    
    # Dublin: must be in Dublin from day 2 to 6
    for i in range(1, 6):
        s.add(Or(start[i] == City.Dublin, end[i] == City.Dublin))
    
    # Reykjavik: wedding between day 9 and 10
    s.add(Or(Or(start[8] == City.Reykjavik, end[8] == City.Reykjavik),
             Or(start[9] == City.Reykjavik, end[9] == City.Reykjavik)))
    
    # Contiguous stay constraint
    for c in cities:
        for i in range(0, 14):  # For indices 0 to 13 (days 1-14)
            s.add(Implies(
                And(
                    Or(start[i] == c, end[i] == c),
                    Or(start[i+2] == c, end[i+2] == c)
                ),
                Or(start[i+1] == c, end[i+1] == c)
            ))
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        # Map Z3 cities to names
        city_names = {
            City.Dublin: "Dublin",
            City.Reykjavik: "Reykjavik",
            City.London: "London",
            City.Mykonos: "Mykonos",
            City.Hamburg: "Hamburg",
            City.Helsinki: "Helsinki"
        }
        
        # Track days per city using sets
        city_days = {c: set() for c in cities}
        for i in range(16):
            day_num = i + 1
            s_city = model.evaluate(start[i])
            e_city = model.evaluate(end[i])
            city_days[s_city].add(day_num)
            city_days[e_city].add(day_num)
        
        # Create segments
        segments = []
        for city in cities:
            if city_days[city]:
                first = min(city_days[city])
                last = max(city_days[city])
                segments.append((first, last, city))
        
        # Sort segments by first day
        segments.sort(key=lambda x: x[0])
        
        # Build itinerary list
        itinerary = []
        for first, last, city in segments:
            city_name = city_names[city]
            if first == last:
                day_range_str = f"Day {first}"
            else:
                day_range_str = f"Day {first}-{last}"
            itinerary.append({'day_range': day_range_str, 'place': city_name})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()