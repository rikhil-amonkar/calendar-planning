from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Edinburgh': ['Berlin', 'Amsterdam', 'Brussels'],
        'Amsterdam': ['Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'],
        'Vienna': ['Berlin', 'Reykjavik', 'Brussels', 'Amsterdam'],
        'Berlin': ['Edinburgh', 'Amsterdam', 'Vienna', 'Brussels', 'Reykjavik'],
        'Brussels': ['Berlin', 'Edinburgh', 'Vienna', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Amsterdam', 'Brussels', 'Berlin']
    }
    
    # Total days
    total_days = 23
    
    # Create Z3 variables for each day: day[i] is the city at day i+1 (1-based)
    day = [Int(f'day_{i}') for i in range(total_days)]
    
    s = Solver()
    
    # Each day variable must be between 0 and 5 (representing the cities)
    for d in day:
        s.add(And(d >= 0, d <= 5))
    
    # Constraints for total days in each city
    amsterdam_days = 4
    edinburgh_days = 5
    brussels_days = 5
    vienna_days = 5
    berlin_days = 4
    reykjavik_days = 5
    
    # Sum of days per city
    s.add(Sum([If(day[i] == city_map['Amsterdam'], 1, 0) for i in range(total_days)]) == amsterdam_days
    s.add(Sum([If(day[i] == city_map['Edinburgh'], 1, 0) for i in range(total_days)]) == edinburgh_days
    s.add(Sum([If(day[i] == city_map['Brussels'], 1, 0) for i in range(total_days)]) == brussels_days
    s.add(Sum([If(day[i] == city_map['Vienna'], 1, 0) for i in range(total_days)]) == vienna_days
    s.add(Sum([If(day[i] == city_map['Berlin'], 1, 0) for i in range(total_days)]) == berlin_days
    s.add(Sum([If(day[i] == city_map['Reykjavik'], 1, 0) for i in range(total_days)]) == reykjavik_days
    
    # Amsterdam must include days 5-8 (1-based, days 5,6,7,8)
    for i in [4,5,6,7]:  # 0-based days 4 to 7
        s.add(day[i] == city_map['Amsterdam'])
    
    # Berlin must include days 16-19 (0-based 15,16,17,18)
    for i in [15,16,17,18]:
        s.add(day[i] == city_map['Berlin'])
    
    # Reykjavik must include days 12-16 (0-based 11,12,13,14,15)
    for i in [11,12,13,14,15]:
        s.add(day[i] == city_map['Reykjavik'])
    
    # Flight transitions: if day[i] != day[i+1], then (day[i], day[i+1]) must be in direct_flights
    for i in range(total_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # If cities are different, check flight exists
        s.add(Implies(current_city != next_city, 
                      Or([And(current_city == city_map[a], next_city == city_map[b]) 
                          for a in direct_flights for b in direct_flights[a]])))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Extract the day assignments
        schedule = [m[d].as_long() for d in day]
        city_names = cities
        
        # Generate the itinerary in the required format
        itinerary = []
        current_city = city_names[schedule[0]]
        start_day = 1
        
        for i in range(1, total_days):
            if city_names[schedule[i]] != current_city:
                # Flight day is i+1 (1-based)
                flight_day = i + 1
                # Add the stay before the flight
                if start_day == flight_day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{flight_day - 1}", "place": current_city})
                # Add the flight day for departure
                itinerary.append({"day_range": f"Day {flight_day}", "place": current_city})
                # Add the flight day for arrival
                new_city = city_names[schedule[i]]
                itinerary.append({"day_range": f"Day {flight_day}", "place": new_city})
                current_city = new_city
                start_day = flight_day
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))