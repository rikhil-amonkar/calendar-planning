from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Rome': ['Oslo', 'Riga', 'Lisbon', 'Vienna'],
        'Riga': ['Oslo', 'Milan', 'Lisbon', 'Vilnius', 'Vienna', 'Rome'],
        'Lisbon': ['Vienna', 'Oslo', 'Riga', 'Rome', 'Milan'],
        'Vilnius': ['Vienna', 'Oslo', 'Riga', 'Milan'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Milan', 'Vienna', 'Vilnius']
    }
    
    # Days: 1 to 15
    days = 15
    day_range = range(1, days + 1)
    
    # Create Z3 variables: for each day, which city are we in?
    # day_city[d] is the city index for day d (1-based)
    day_city = [Int(f'day_{d}_city') for d in day_range]
    
    s = Solver()
    
    # Each day_city must be a valid city index (0 to 6)
    for d in day_range:
        s.add(day_city[d-1] >= 0, day_city[d-1] <= 6)
    
    # Fixed constraints:
    # Day 1 and 4 in Vienna (city 0)
    s.add(day_city[0] == city_map['Vienna'])
    s.add(day_city[3] == city_map['Vienna'])
    
    # Lisbon between day 11-13 (days 11,12,13)
    for d in [10, 11, 12]:  # 0-based for 11-13 (days 11,12,13)
        s.add(day_city[d] == city_map['Lisbon'])
    
    # Oslo between day 13-15 (days 13,14,15)
    for d in [12, 13, 14]:  # 0-based for 13-15
        s.add(day_city[d] == city_map['Oslo'])
    
    # Duration constraints:
    # Vienna: 4 days (including days 1 and 4)
    vienna_days = sum([If(day_city[d] == city_map['Vienna'], 1, 0) for d in range(days)])
    s.add(vienna_days == 4)
    
    # Milan: 2 days
    milan_days = sum([If(day_city[d] == city_map['Milan'], 1, 0) for d in range(days)])
    s.add(milan_days == 2)
    
    # Rome: 3 days
    rome_days = sum([If(day_city[d] == city_map['Rome'], 1, 0) for d in range(days)])
    s.add(rome_days == 3)
    
    # Riga: 2 days
    riga_days = sum([If(day_city[d] == city_map['Riga'], 1, 0) for d in range(days)])
    s.add(riga_days == 2)
    
    # Vilnius: 4 days
    vilnius_days = sum([If(day_city[d] == city_map['Vilnius'], 1, 0) for d in range(days)])
    s.add(vilnius_days == 4)
    
    # Flight constraints: transitions between days must be via direct flights or same city
    for d in range(days - 1):
        current_city = day_city[d]
        next_city = day_city[d + 1]
        # Either stay in the same city or move to a directly connected city
        same_city = (current_city == next_city)
        # Create a condition for each possible direct flight
        flight_conditions = []
        for city in cities:
            if city in direct_flights[cities[m.evaluate(current_city).as_long()]]:
                flight_conditions.append(next_city == city_map[city])
        s.add(Or(same_city, *flight_conditions))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Decode the solution
        itinerary_days = []
        for d in range(days):
            city_idx = m.evaluate(day_city[d]).as_long()
            itinerary_days.append(cities[city_idx])
        
        # Now, create the itinerary in the required format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        for d in range(1, days):
            if itinerary_days[d] == current_place:
                continue
            else:
                end_day = d
                if start_day == end_day:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_str, "place": current_place})
                # Add the flight day: day d+1 is both current_place and next place
                flight_day = d + 1
                itinerary.append({"day_range": f"Day {flight_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {flight_day}", "place": itinerary_days[d]})
                current_place = itinerary_days[d]
                start_day = d + 1
        # Add the last segment
        if start_day <= days:
            end_day = days
            if start_day == end_day:
                day_str = f"Day {start_day}"
            else:
                day_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_str, "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))