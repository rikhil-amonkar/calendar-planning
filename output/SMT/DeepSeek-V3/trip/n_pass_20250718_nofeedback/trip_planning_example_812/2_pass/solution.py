from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Porto', 'Paris', 'Florence', 'Vienna', 'Munich', 'Nice', 'Warsaw']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Paris': ['Warsaw', 'Florence', 'Vienna', 'Porto', 'Nice', 'Munich'],
        'Munich': ['Vienna', 'Florence', 'Warsaw', 'Nice', 'Porto', 'Paris'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Warsaw': ['Paris', 'Vienna', 'Munich', 'Nice', 'Porto'],
        'Nice': ['Vienna', 'Munich', 'Warsaw', 'Paris', 'Porto']
    }
    
    # Create Z3 variables: day[i] is the city index (0..6) for day i+1 (since days are 1-based)
    days = [Int(f'day_{i}') for i in range(20)]
    
    # Solver
    s = Solver()
    
    # Each day must be a valid city index (0 to 6)
    for day in days:
        s.add(day >= 0, day < 7)
    
    # Fixed constraints
    # Porto between day 1 and 3 (indices 0, 1, 2 in 0-based)
    s.add(days[0] == city_to_idx['Porto'])
    s.add(days[1] == city_to_idx['Porto'])
    s.add(days[2] == city_to_idx['Porto'])
    
    # Warsaw wedding between day 13 and 15 (indices 12, 13, 14)
    s.add(days[12] == city_to_idx['Warsaw'])
    s.add(days[13] == city_to_idx['Warsaw'])
    s.add(days[14] == city_to_idx['Warsaw'])
    
    # Vienna relatives between day 19 and 20 (indices 18, 19)
    s.add(days[18] == city_to_idx['Vienna'])
    s.add(days[19] == city_to_idx['Vienna'])
    
    # Transition constraints: consecutive days must be same city or connected by direct flight
    for i in range(19):
        current_city = days[i]
        next_city = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_idx[city], next_city == city_to_idx[adj])
              for city in direct_flights 
              for adj in direct_flights[city]]
        ))
    
    # Duration constraints
    # Paris: 5 days
    paris_days = Sum([If(days[i] == city_to_idx['Paris'], 1, 0) for i in range(20)])
    s.add(paris_days == 5)
    
    # Florence: 3 days
    florence_days = Sum([If(days[i] == city_to_idx['Florence'], 1, 0) for i in range(20)])
    s.add(florence_days == 3)
    
    # Vienna: 2 days (but days 19 and 20 are already Vienna, so total is 2)
    vienna_days = Sum([If(days[i] == city_to_idx['Vienna'], 1, 0) for i in range(20)])
    s.add(vienna_days == 2)
    
    # Munich: 5 days
    munich_days = Sum([If(days[i] == city_to_idx['Munich'], 1, 0) for i in range(20)])
    s.add(munich_days == 5)
    
    # Nice: 5 days
    nice_days = Sum([If(days[i] == city_to_idx['Nice'], 1, 0) for i in range(20)])
    s.add(nice_days == 5)
    
    # Warsaw: 3 days (days 13-15 are 3 days)
    warsaw_days = Sum([If(days[i] == city_to_idx['Warsaw'], 1, 0) for i in range(20)])
    s.add(warsaw_days == 3)
    
    # Porto: 3 days (days 1-3 are 3 days)
    porto_days = Sum([If(days[i] == city_to_idx['Porto'], 1, 0) for i in range(20)])
    s.add(porto_days == 3)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'city': cities[city_idx]})
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return result
    else:
        return None

# Generate and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    import json
    print(json.dumps(itinerary, indent=2))
else:
    print("No valid itinerary found.")