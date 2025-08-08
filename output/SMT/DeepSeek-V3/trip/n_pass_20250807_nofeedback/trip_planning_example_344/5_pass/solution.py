from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    Valencia, Athens, Naples, Zurich = 0, 1, 2, 3
    
    # Direct flights: adjacency list
    direct_flights = {
        Valencia: [Athens, Naples, Zurich],
        Athens: [Valencia, Naples, Zurich],
        Naples: [Valencia, Athens, Zurich],
        Zurich: [Valencia, Athens, Naples]
    }
    
    # Create Z3 variables for each day's city
    days = 20
    day_city = [Int(f'day_{i}_city') for i in range(days)]
    
    s = Solver()
    s.set("timeout", 30000)  # Set a 30-second timeout
    
    # Each day's city must be one of the four cities
    for day in day_city:
        s.add(Or([day == city for city in range(4)]))
    
    # Transition constraints: consecutive days must be the same city or connected by a direct flight
    for i in range(days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city1, next_city == city2) 
              for city1 in range(4) 
              for city2 in direct_flights[city1]]
        ))
    
    # Count days in each city
    valencia_days = Sum([If(day == Valencia, 1, 0) for day in day_city])
    athens_days = Sum([If(day == Athens, 1, 0) for day in day_city])
    naples_days = Sum([If(day == Naples, 1, 0) for day in day_city])
    zurich_days = Sum([If(day == Zurich, 1, 0) for day in day_city])
    
    s.add(valencia_days == 6)
    s.add(athens_days == 6)
    s.add(naples_days == 5)
    s.add(zurich_days == 6)
    
    # Athens must be visited between day 1 and day 6 (inclusive)
    s.add(Or([day_city[i] == Athens for i in range(6)]))  # At least one day in Athens in days 1-6
    
    # Naples must be visited between day 16 and day 20 (inclusive)
    s.add(Or([day_city[i] == Naples for i in range(15, 20)]))  # 0-based, days 16-20 are indices 15-19
    
    # Check if the problem is solvable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = ['Valencia', 'Athens', 'Naples', 'Zurich']
        for i in range(days):
            day_num = i + 1
            city_idx = m.evaluate(day_city[i]).as_long()
            itinerary.append({'day': day_num, 'place': city_names[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in city_names}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        print("Counts:", counts)  # Debugging
        
        # Prepare the JSON output
        output = {
            'itinerary': itinerary
        }
        return output
    else:
        return None

# Generate and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(itinerary)
else:
    print("No valid itinerary found.")