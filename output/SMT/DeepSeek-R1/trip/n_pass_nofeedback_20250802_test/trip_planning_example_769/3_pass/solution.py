from z3 import *
import json

def main():
    # Define cities
    City, (Porto, Prague, Reykjavik, Santorini, Amsterdam, Munich) = EnumSort('City', 
        ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich'])
    
    # City name mapping
    city_dict = {
        'Porto': Porto,
        'Prague': Prague,
        'Reykjavik': Reykjavik,
        'Santorini': Santorini,
        'Amsterdam': Amsterdam,
        'Munich': Munich
    }
    
    # Flight connections (undirected)
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
    
    # Create directed flights (both directions)
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
    
    s = Solver()
    
    # Day variables (0-indexed: day0=Day1)
    S = [Const(f'S_{d}', City) for d in range(16)]  # Start city each day
    E = [Const(f'E_{d}', City) for d in range(16)]  # End city each day
    
    # Constraint 1: Continuity between days
    for d in range(15):
        s.add(E[d] == S[d+1])
    
    # Constraint 2: Valid transitions (stay or direct flight)
    for d in range(16):
        stay = (S[d] == E[d])
        flight = Or([And(S[d] == a, E[d] == b) for a, b in directed_edges])
        s.add(Or(stay, flight))
    
    # Constraint 3: Total days per city
    cities = [Porto, Prague, Reykjavik, Santorini, Amsterdam, Munich]
    for c in cities:
        total = 0
        for d in range(16):
            # Count if city appears at start or end of day
            total += If(Or(S[d] == c, E[d] == c), 1, 0)
        s.add(total == required_days[c])
    
    # Constraint 4: Event requirements
    # Reykjavik wedding between days 4-7 (0-indexed days 3-6)
    reykjavik_days = [Or(S[d] == Reykjavik, E[d] == Reykjavik) for d in [3,4,5,6]]
    s.add(Or(reykjavik_days))
    
    # Munich meeting between days 7-10 (0-indexed days 6-9)
    munich_days = [Or(S[d] == Munich, E[d] == Munich) for d in [6,7,8,9]]
    s.add(Or(munich_days))
    
    # Amsterdam conference on days 14-15 (must be full days)
    s.add(S[13] == Amsterdam)  # Day14 start
    s.add(E[13] == Amsterdam)  # Day14 end
    s.add(S[14] == Amsterdam)  # Day15 start
    s.add(E[14] == Amsterdam)  # Day15 end
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Helper to get city name from Z3 value
        def get_city_name(val):
            return val.decl().name()
        
        # Build detailed itinerary
        for day in range(1, 17):  # Days 1-16
            idx = day - 1
            start_city = get_city_name(m[S[idx]])
            end_city = get_city_name(m[E[idx]])
            
            # Always add start of day
            itinerary.append({"day": day, "place": start_city})
            
            # If traveled, add end city separately
            if start_city != end_city:
                itinerary.append({"day": day, "place": end_city})
        
        # Output in required format
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()