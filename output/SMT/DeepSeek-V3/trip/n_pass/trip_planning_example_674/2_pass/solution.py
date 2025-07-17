from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')
    ]
    
    # Create a dictionary for quick lookup of direct flights
    flight_dict = {city: [] for city in cities}
    for flight in direct_flights:
        city1, city2 = flight
        flight_dict[city1].append(city2)
        flight_dict[city2].append(city1)
    
    s = Solver()
    
    # Create variables: day_1 to day_14, each can be one of the cities.
    day_city = [Int(f'day_{day}') for day in range(1, 15)]
    for day in range(14):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Duration constraints
    city_durations = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    for city, duration in city_durations.items():
        s.add(Sum([If(day_city[day] == city_to_idx[city], 1, 0) for day in range(14)]) == duration)
    
    # Specific day constraints
    # Helsinki on days 1 and 2 (indices 0 and 1)
    s.add(day_city[0] == city_to_idx['Helsinki'])
    s.add(day_city[1] == city_to_idx['Helsinki'])
    
    # Warsaw on days 9, 10, 11 (indices 8, 9, 10)
    s.add(day_city[8] == city_to_idx['Warsaw'])
    s.add(day_city[9] == city_to_idx['Warsaw'])
    s.add(day_city[10] == city_to_idx['Warsaw'])
    
    # Reykjavik on day 8 (index 7)
    s.add(day_city[7] == city_to_idx['Reykjavik'])
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for day in range(13):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either same city or adjacent via direct flight
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_to_idx[city1], next_city == city_to_idx[city2])
                for city1 in flight_dict
                for city2 in flight_dict[city1]
            ]
        ))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(14):
            city_idx = model.eval(day_city[day]).as_long()
            itinerary.append({'day': day + 1, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function
result = solve_itinerary()
print(result)