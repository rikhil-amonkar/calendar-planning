from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Geneva', 'Paris', 'Oslo', 'Porto', 'Reykjavik']
    city_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections
    connections = {
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Paris': ['Geneva', 'Oslo', 'Porto', 'Reykjavik'],
        'Oslo': ['Geneva', 'Paris', 'Porto', 'Reykjavik'],
        'Porto': ['Geneva', 'Paris', 'Oslo'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    # Create solver and day variables
    s = Solver()
    days = [Int(f'day_{i}') for i in range(1, 24)]
    
    # Each day must be assigned to a valid city
    for day in days:
        s.add(day >= 0, day <= 4)
    
    # Fixed periods
    # Geneva days 1-7 (indices 0-6)
    for i in range(7):
        s.add(days[i] == city_idx['Geneva'])
    
    # Oslo days 19-23 (indices 18-22)
    for i in range(18, 23):
        s.add(days[i] == city_idx['Oslo'])
    
    # Total days required
    total_days = {
        'Geneva': 7,
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Reykjavik': 2
    }
    
    # Count days in each city
    for city, required in total_days.items():
        count = Sum([If(day == city_idx[city], 1, 0) for day in days])
        s.add(count == required)
    
    # Valid transitions between cities
    for i in range(22):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or use direct flight
        s.add(Or(
            current == next_day,
            Or([And(current == city_idx[a], next_day == city_idx[b])
                for a in connections for b in connections[a]])
        ))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(1, 24):
            day_var = days[i-1]
            city = cities[model[day_var].as_long()]
            itinerary.append({"day": i, "place": city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print itinerary
print(solve_itinerary())