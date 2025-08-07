from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Paris': ['Oslo', 'Porto', 'Geneva', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    # Create Z3 variables: day_1 to day_23, each is an integer representing city index
    days = [Int(f'day_{i}') for i in range(1, 24)]
    
    s = Solver()
    
    # Each day's assignment must be a valid city index (0 to 4)
    for day in days:
        s.add(And(day >= 0, day <= 4))
    
    # Geneva must be days 1-7 (indices 0-6 in days list)
    for i in range(7):
        s.add(days[i] == city_to_idx['Geneva'])
    
    # Oslo must be days 19-23 (indices 18-22 in days list, 1-based is days 19-23)
    for i in range(18, 23):
        s.add(days[i] == city_to_idx['Oslo'])
    
    # Total days constraints
    total_days = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    
    for city, total in total_days.items():
        idx = city_to_idx[city]
        s.add(Sum([If(day == idx, 1, 0) for day in days]) == total)
    
    # Transition constraints: consecutive days must be same city or connected by direct flight
    for i in range(22):  # days 1..22 and 2..23
        current_city = days[i]
        next_city = days[i+1]
        # Either same city or connected
        same_city = current_city == next_city
        connected = Or([And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
                        for a in direct_flights 
                        for b in direct_flights[a]])
        s.add(Or(same_city, connected))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 24):
            day_var = days[i-1]
            city_idx = model[day_var].as_long()
            city = cities[city_idx]
            itinerary.append({"day": i, "place": city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)