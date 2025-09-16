from z3 import *
import json

def main():
    # Define the cities
    City, (Porto, Prague, Reykjavik, Santorini, Amsterdam, Munich) = EnumSort('City', 
        ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich'])
    
    # Map city names to enum constants
    city_dict = {
        'Porto': Porto,
        'Prague': Prague,
        'Reykjavik': Reykjavik,
        'Santorini': Santorini,
        'Amsterdam': Amsterdam,
        'Munich': Munich
    }
    
    # Base undirected flight edges
    base_edges = [
        ("Porto", "Amsterdam"),
        ("Munich", "Amsterdam"),
        ("Reykjavik", "Amsterdam"),
        ("Munich", "Porto"),
        ("Prague", "Reykjavik"),
        ("Reykjavik", "Munich"),
        ("Amsterdam", "Santorini"),
        ("Prague", "Amsterdam"),
        ("Prague", "Munich")
    ]
    
    # Create directed edges for both directions
    directed_edges = []
    for a, b in base_edges:
        a_const = city_dict[a]
        b_const = city_dict[b]
        directed_edges.append((a_const, b_const))
        directed_edges.append((b_const, a_const))
    
    # Required days per city
    required_days = {
        Porto: 5,
        Prague: 4,
        Reykjavik: 4,
        Santorini: 2,
        Amsterdam: 2,
        Munich: 4
    }
    
    # Initialize solver
    s = Solver()
    
    # Create S and E for 16 days (index 0 to 15)
    S = [Const(f'S_{d}', City) for d in range(16)]
    E = [Const(f'E_{d}', City) for d in range(16)]
    
    # Constraint 1: E[d] == S[d+1] for d in 0 to 14
    for d in range(15):
        s.add(E[d] == S[d+1])
    
    # Constraint 2: For each day, either stay in the same city or take a direct flight
    for d in range(16):
        same_city = (S[d] == E[d])
        flight_exists = Or([And(S[d] == a, E[d] == b) for a, b in directed_edges])
        s.add(Or(same_city, flight_exists))
    
    # Constraint 3: Total days per city
    cities = [Porto, Prague, Reykjavik, Santorini, Amsterdam, Munich]
    for c in cities:
        total = 0
        for d in range(16):
            total += If(Or(S[d] == c, E[d] == c), 1, 0)
        s.add(total == required_days[c])
    
    # Constraint 4: Events
    # Amsterdam: must be present on day 14 and 15 (0-indexed: 13 and 14)
    s.add(Or(S[13] == Amsterdam, E[13] == Amsterdam))
    s.add(Or(S[14] == Amsterdam, E[14] == Amsterdam))
    # Reykjavik: at least one day in [4,7] (0-indexed: 3 to 6)
    reykjavik_days = [Or(S[d] == Reykjavik, E[d] == Reykjavik) for d in [3,4,5,6]]
    s.add(Or(reykjavik_days))
    # Munich: at least one day in [7,10] (0-indexed: 6 to 9)
    munich_days = [Or(S[d] == Munich, E[d] == Munich) for d in [6,7,8,9]]
    s.add(Or(munich_days))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 17):
            idx = day - 1
            start_city = m[S[idx]]
            start_city_name = start_city.decl().name()
            itinerary.append({"day": day, "place": start_city_name})
            end_city = m[E[idx]]
            end_city_name = end_city.decl().name()
            if start_city_name != end_city_name:
                itinerary.append({"day": day, "place": end_city_name})
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()