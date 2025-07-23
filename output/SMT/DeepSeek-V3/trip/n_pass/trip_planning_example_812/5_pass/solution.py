from z3 import *

def solve_itinerary():
    # Cities with their required stay durations
    cities = {
        'Porto': 3,
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    city_names = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_names)}
    
    # Direct flight connections
    direct_flights = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Paris': ['Warsaw', 'Florence', 'Vienna', 'Porto', 'Nice', 'Munich'],
        'Munich': ['Vienna', 'Florence', 'Warsaw', 'Nice', 'Porto', 'Paris'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Warsaw': ['Paris', 'Vienna', 'Munich', 'Nice', 'Porto'],
        'Nice': ['Vienna', 'Munich', 'Warsaw', 'Paris', 'Porto']
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(20)]
    
    # Initialize solver with timeout
    s = Solver()
    s.set("timeout", 30000)  # 30 second timeout
    
    # Each day must be a valid city index
    for day in days:
        s.add(day >= 0, day < len(city_names))
    
    # Fixed constraints
    # Porto days 1-3 (indices 0-2)
    s.add(days[0] == city_to_idx['Porto'])
    s.add(days[1] == city_to_idx['Porto'])
    s.add(days[2] == city_to_idx['Porto'])
    
    # Warsaw days 13-15 (indices 12-14)
    s.add(days[12] == city_to_idx['Warsaw'])
    s.add(days[13] == city_to_idx['Warsaw'])
    s.add(days[14] == city_to_idx['Warsaw'])
    
    # Vienna days 19-20 (indices 18-19)
    s.add(days[18] == city_to_idx['Vienna'])
    s.add(days[19] == city_to_idx['Vienna'])
    
    # Flight transition constraints
    for i in range(19):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or fly to connected city
        s.add(Or(
            current == next_day,
            *[And(current == city_to_idx[city], next_day == city_to_idx[adj])
              for city in direct_flights 
              for adj in direct_flights[city]]
        ))
    
    # Duration constraints for each city
    for city, duration in cities.items():
        if city in ['Porto', 'Warsaw', 'Vienna']:
            continue  # Already handled by fixed constraints
        city_days = Sum([If(days[i] == city_to_idx[city], 1, 0) for i in range(20)])
        s.add(city_days == duration)
    
    # Additional constraints to help the solver
    # No immediate return to same city after flight (except for fixed stays)
    for i in range(18):
        s.add(Implies(
            days[i] != days[i+1],  # If we flew on day i
            days[i+1] != days[i+2]  # Then don't fly back immediately
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'city': city_names[city_idx]})
        
        # Verify all constraints
        city_counts = {city: 0 for city in city_names}
        for entry in itinerary:
            city_counts[entry['city']] += 1
        
        print("Verification:")
        for city, count in city_counts.items():
            print(f"{city}: {count} days (required: {cities[city]})")
        
        return {'itinerary': itinerary}
    else:
        print("No valid itinerary found that satisfies all constraints.")
        return None

# Generate and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    import json
    print(json.dumps(itinerary, indent=2))
else:
    print("Failed to find a valid itinerary.")