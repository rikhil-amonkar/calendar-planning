import json
from z3 import *

def main():
    # Define cities
    cities = ['Paris', 'Oslo', 'Porto', 'Geneva', 'Reykjavik']
    city_dict = {c: i for i, c in enumerate(cities)}
    n_days = 23
    days = list(range(1, n_days+1))
    
    # Direct flights (bidirectional)
    direct_flights = [
        (city_dict['Paris'], city_dict['Oslo']),
        (city_dict['Geneva'], city_dict['Oslo']),
        (city_dict['Porto'], city_dict['Paris']),
        (city_dict['Geneva'], city_dict['Paris']),
        (city_dict['Geneva'], city_dict['Porto']),
        (city_dict['Paris'], city_dict['Reykjavik']),
        (city_dict['Reykjavik'], city_dict['Oslo']),
        (city_dict['Porto'], city_dict['Oslo'])
    ]
    
    # Create solver
    s = Solver()
    
    # Variables for each day: start city and flight destination
    start_city = [Int(f'start_city_{i}') for i in days]
    flight_taken = [Bool(f'flight_taken_{i}') for i in days]
    flight_dest = [Int(f'flight_dest_{i}') for i in days]
    
    # Initial constraint: start in Geneva on day 1
    s.add(start_city[0] == city_dict['Geneva'])
    
    # Constraints for each day
    for i in range(n_days):
        # City values are between 0 and 4
        s.add(start_city[i] >= 0, start_city[i] <= 4)
        s.add(flight_dest[i] >= 0, flight_dest[i] <= 4)
        
        # If flight taken, destination must be different and connected
        if i < n_days - 1:
            s.add(If(flight_taken[i], start_city[i+1] == flight_dest[i], start_city[i+1] == start_city[i]))
        s.add(Implies(flight_taken[i], start_city[i] != flight_dest[i]))
        s.add(Implies(flight_taken[i], Or([Or(And(start_city[i] == c1, flight_dest[i] == c2), And(start_city[i] == c2, flight_dest[i] == c1)) for (c1, c2) in direct_flights])))
    
    # Define being in a city on a day
    def in_city(day, city):
        return Or(start_city[day] == city, And(flight_taken[day], flight_dest[day] == city))
    
    # Fixed day constraints
    for i in range(0, 7):  # Days 1-7 in Geneva
        s.add(in_city(i, city_dict['Geneva']))
    for i in range(18, 23):  # Days 19-23 in Oslo (index 18 to 22 for 0-indexed)
        s.add(in_city(i, city_dict['Oslo']))
    
    # Total day constraints
    total_days = [0] * 5
    for city_idx in range(5):
        total_days[city_idx] = Sum([If(in_city(i, city_idx), 1, 0) for i in range(n_days)])
    s.add(total_days[city_dict['Paris']] == 6)
    s.add(total_days[city_dict['Oslo']] == 5)
    s.add(total_days[city_dict['Porto']] == 7)
    s.add(total_days[city_dict['Geneva']] == 7)
    s.add(total_days[city_dict['Reykjavik']] == 2)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Evaluate model values
        start_city_vals = [m.evaluate(start_city[i]).as_long() for i in range(n_days)]
        flight_taken_vals = [is_true(m.evaluate(flight_taken[i])) for i in range(n_days)]
        flight_dest_vals = [m.evaluate(flight_dest[i]).as_long() for i in range(n_days)]
        
        # Reconstruct itinerary
        itinerary = []
        current_city = start_city_vals[0]
        start_day = 1
        for day_idx in range(n_days):
            if day_idx < n_days - 1 and flight_taken_vals[day_idx]:
                end_day = day_idx + 1
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city]
                })
                current_city = flight_dest_vals[day_idx]
                start_day = end_day
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": cities[current_city]
        })
        
        # Output JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()