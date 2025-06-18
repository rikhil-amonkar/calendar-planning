from z3 import *

def main():
    # Define the City enum
    City = Datatype('City')
    cities_list = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    for city in cities_list:
        City.declare(city)
    City = City.create()
    
    # Parse the direct flights string into pairs
    direct_flights_str = "Reykjavik and Munich, Munich and Frankfurt, Split and Oslo, Reykjavik and Oslo, Bucharest and Munich, Oslo and Frankfurt, Bucharest and Barcelona, Barcelona and Frankfurt, Reykjavik and Frankfurt, Barcelona and Stockholm, Barcelona and Reykjavik, Stockholm and Reykjavik, Barcelona and Split, Bucharest and Oslo, Bucharest and Frankfurt, Split and Stockholm, Barcelona and Oslo, Stockholm and Munich, Stockholm and Oslo, Split and Frankfurt, Barcelona and Munich, Stockholm and Frankfurt, Munich and Oslo, Split and Munich"
    pairs_str_list = direct_flights_str.split(', ')
    direct_flights_pairs = []
    for s in pairs_str_list:
        parts = s.split(' and ')
        direct_flights_pairs.append((parts[0], parts[1]))
    
    # Create list of allowed edges (both directions)
    allowed_edges = []
    for (a, b) in direct_flights_pairs:
        city_a = getattr(City, a)
        city_b = getattr(City, b)
        allowed_edges.append((city_a, city_b))
        allowed_edges.append((city_b, city_a))
    
    # Create variables for the start city of each day (c1 to c21)
    c = [Const('c_%d' % i, City) for i in range(1, 22)]
    
    s = Solver()
    
    # Flight constraints for days 1 to 20
    for i in range(1, 21):
        idx1 = i - 1
        idx2 = i
        stay = (c[idx1] == c[idx2])
        flight_options = []
        for (a, b) in allowed_edges:
            flight_options.append(And(c[idx1] == a, c[idx2] == b))
        s.add(Or(stay, Or(flight_options)))
    
    # Total days per city
    total_days_constraints = []
    for city_name in cities_list:
        city_const = getattr(City, city_name)
        total = 0
        for d in range(0, 20):
            total += If(Or(c[d] == city_const, c[d+1] == city_const), 1, 0)
        if city_name == 'Oslo':
            s.add(total == 2)
        elif city_name == 'Reykjavik':
            s.add(total == 5)
        elif city_name == 'Stockholm':
            s.add(total == 4)
        elif city_name == 'Munich':
            s.add(total == 4)
        elif city_name == 'Frankfurt':
            s.add(total == 4)
        elif city_name == 'Barcelona':
            s.add(total == 3)
        elif city_name == 'Bucharest':
            s.add(total == 2)
        elif city_name == 'Split':
            s.add(total == 3)
    
    # Fixed event: Oslo on day 16 and 17
    s.add(Or(c[15] == City.Oslo, c[16] == City.Oslo))  # Day 16
    s.add(Or(c[16] == City.Oslo, c[17] == City.Oslo))  # Day 17
    
    # Reykjavik between day 9 and 13 (inclusive)
    reyk_days = []
    for d in range(8, 13):  # Days 9 to 13: indices 8 to 12
        reyk_days.append(Or(c[d] == City.Reykjavik, c[d+1] == City.Reykjavik))
    s.add(Or(reyk_days))
    
    # Munich between day 13 and 16 (inclusive)
    munich_days = []
    for d in range(12, 16):  # Days 13 to 16: indices 12 to 15
        munich_days.append(Or(c[d] == City.Munich, c[d+1] == City.Munich))
    s.add(Or(munich_days))
    
    # Frankfurt between day 17 and 20 (inclusive)
    frankfurt_days = []
    for d in range(16, 20):  # Days 17 to 20: indices 16 to 19
        frankfurt_days.append(Or(c[d] == City.Frankfurt, c[d+1] == City.Frankfurt))
    s.add(Or(frankfurt_days))
    
    # Check and print the solution
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(0, 20):
            start_city = m.eval(c[i])
            end_city = m.eval(c[i+1])
            if start_city == end_city:
                schedule.append(f"Day {i+1}: Stay in {start_city}")
            else:
                schedule.append(f"Day {i+1}: Travel from {start_city} to {end_city} (thus in both {start_city} and {end_city})")
        print("Found a valid trip plan:")
        for entry in schedule:
            print(entry)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()