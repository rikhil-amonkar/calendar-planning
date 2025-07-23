from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Munich': ['Porto', 'Krakow', 'Milan', 'Split', 'Dubrovnik'],
        'Porto': ['Munich', 'Milan'],
        'Split': ['Milan', 'Krakow', 'Munich'],
        'Milan': ['Split', 'Porto', 'Krakow', 'Munich'],
        'Krakow': ['Munich', 'Split', 'Milan'],
        'Dubrovnik': ['Munich']
    }
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: day 1 to 16, each can be one of the cities
    days = 16
    itinerary = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Each day's value is between 0 and 5 (index of cities)
    for day in itinerary:
        s.add(day >= 0, day < len(cities))
    
    # Helper function to get city name from index
    def city_name(idx):
        return cities[idx]
    
    # Constraints for transitions: consecutive days must be same city or connected by direct flight
    for i in range(days - 1):
        current_city = itinerary[i]
        next_city = itinerary[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            # Check if there's a direct flight between current_city and next_city
            *[And(current_city == city_map[a], next_city == city_map[b]) 
              for a in direct_flights 
              for b in direct_flights[a]]
        ))
    
    # Total days constraints
    def count_days(city_name):
        city_idx = city_map[city_name]
        return Sum([If(itinerary[i] == city_idx, 1, 0) for i in range(days)])
    
    s.add(count_days('Dubrovnik') == 4)
    s.add(count_days('Split') == 3)
    s.add(count_days('Milan') == 3)
    s.add(count_days('Porto') == 4)
    s.add(count_days('Krakow') == 2)
    s.add(count_days('Munich') == 5)
    
    # Event constraints:
    # Wedding in Milan between day 11-13 (days 11,12,13 are in Milan)
    s.add(itinerary[10] == city_map['Milan'])  # day 11
    s.add(itinerary[11] == city_map['Milan'])   # day 12
    s.add(itinerary[12] == city_map['Milan'])   # day 13
    
    # Friends in Krakow between day 8-9: assume day 9 only (since day 8 is in Munich)
    s.add(itinerary[8] == city_map['Krakow'])   # day 9
    
    # Annual show in Munich from day 4 to day 8 (days 4,5,6,7,8)
    for i in range(3, 8):  # days 4 to 8 (indices 3 to 7)
        s.add(itinerary[i] == city_map['Munich'])
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Decode the itinerary
        itinerary_result = []
        for i in range(days):
            day_num = i + 1
            city_idx = model.evaluate(itinerary[i]).as_long()
            city = cities[city_idx]
            itinerary_result.append({"day": day_num, "place": city})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary_result:
            counts[entry['place']] += 1
        
        # Prepare the output
        output = {
            "itinerary": itinerary_result
        }
        return output
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))