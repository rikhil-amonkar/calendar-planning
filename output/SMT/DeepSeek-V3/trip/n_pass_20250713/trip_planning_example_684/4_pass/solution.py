from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections
    direct_flights = {
        'Amsterdam': ['Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'],
        'Edinburgh': ['Amsterdam', 'Berlin', 'Brussels'],
        'Brussels': ['Edinburgh', 'Vienna', 'Berlin', 'Reykjavik'],
        'Vienna': ['Amsterdam', 'Berlin', 'Brussels', 'Reykjavik'],
        'Berlin': ['Amsterdam', 'Edinburgh', 'Vienna', 'Brussels', 'Reykjavik'],
        'Reykjavik': ['Amsterdam', 'Vienna', 'Brussels', 'Berlin']
    }
    
    total_days = 23
    
    # Create Z3 variables - day[i] represents the city on day i+1 (1-based)
    day = [Int(f'day_{i}') for i in range(total_days)]
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for d in day:
        s.add(And(d >= 0, d <= 5))
    
    # Fixed time windows
    # Amsterdam days 5-8 (0-based 4-7)
    for i in range(4, 8):
        s.add(day[i] == city_map['Amsterdam'])
    
    # Berlin days 16-19 (0-based 15-18)
    for i in range(15, 19):
        s.add(day[i] == city_map['Berlin'])
    
    # Reykjavik days 12-16 (0-based 11-15)
    for i in range(11, 16):
        s.add(day[i] == city_map['Reykjavik'])
    
    # Total days in each city
    s.add(Sum([If(day[i] == city_map['Amsterdam'], 1, 0) for i in range(total_days)]) == 4)
    s.add(Sum([If(day[i] == city_map['Edinburgh'], 1, 0) for i in range(total_days)]) == 5)
    s.add(Sum([If(day[i] == city_map['Brussels'], 1, 0) for i in range(total_days)]) == 5)
    s.add(Sum([If(day[i] == city_map['Vienna'], 1, 0) for i in range(total_days)]) == 5)
    s.add(Sum([If(day[i] == city_map['Berlin'], 1, 0) for i in range(total_days)]) == 4)
    s.add(Sum([If(day[i] == city_map['Reykjavik'], 1, 0) for i in range(total_days)]) == 5)
    
    # Flight transitions must be direct flights
    for i in range(total_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        s.add(Implies(current_city != next_city, 
                     Or([And(current_city == city_map[a], next_city == city_map[b])
                         for a in direct_flights for b in direct_flights[a]])))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        schedule = [m[d].as_long() for d in day]
        
        # Generate itinerary
        itinerary = []
        current_city = cities[schedule[0]]
        start_day = 1
        
        for i in range(1, total_days):
            if cities[schedule[i]] != current_city:
                flight_day = i + 1
                if start_day == flight_day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{flight_day-1}", "place": current_city})
                itinerary.append({"day_range": f"Day {flight_day}", "place": current_city})
                itinerary.append({"day_range": f"Day {flight_day}", "place": cities[schedule[i]]})
                current_city = cities[schedule[i]]
                start_day = flight_day
        
        # Add last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))