import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    
    # Direct flights (bidirectional unless specified otherwise)
    direct_flights = {
        'Riga': ['Oslo', 'Milan', 'Vilnius', 'Lisbon', 'Vienna', 'Rome'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Milan', 'Vienna', 'Vilnius'],
        'Rome': ['Oslo', 'Riga', 'Lisbon', 'Vienna'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Vilnius': ['Vienna', 'Riga', 'Oslo', 'Milan'],
        'Lisbon': ['Vienna', 'Riga', 'Rome', 'Oslo', 'Milan']
    }
    
    # Create solver
    s = Solver()
    
    # Day variables: day[i] is the city on day i (1-based)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    # Map cities to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints for each day to be a valid city
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Constraint: Day 1 is Vienna (conference)
    s.add(days[0] == city_to_int['Vienna'])
    
    # Constraint: Day 4 is Vienna (conference)
    s.add(days[3] == city_to_int['Vienna'])
    
    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(14):  # days 1..15, compare i and i+1 (0-based)
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            *[And(current_day == city_to_int[a], next_day == city_to_int[b]) 
              for a in direct_flights for b in direct_flights[a] if b in direct_flights]
        )
    
    # Duration constraints for each city
    # Vienna: 4 days (including days 1 and 4)
    vienna_days = Sum([If(days[i] == city_to_int['Vienna'], 1, 0) for i in range(15)])
    s.add(vienna_days == 4)
    
    # Milan: 2 days
    milan_days = Sum([If(days[i] == city_to_int['Milan'], 1, 0) for i in range(15)])
    s.add(milan_days == 2)
    
    # Rome: 3 days
    rome_days = Sum([If(days[i] == city_to_int['Rome'], 1, 0) for i in range(15)])
    s.add(rome_days == 3)
    
    # Riga: 2 days
    riga_days = Sum([If(days[i] == city_to_int['Riga'], 1, 0) for i in range(15)])
    s.add(riga_days == 2)
    
    # Lisbon: 3 days, with days 11-13 in Lisbon
    lisbon_days = Sum([If(days[i] == city_to_int['Lisbon'], 1, 0) for i in range(15)])
    s.add(lisbon_days == 3)
    s.add(Or(
        days[10] == city_to_int['Lisbon'],  # day 11
        days[11] == city_to_int['Lisbon'],  # day 12
        days[12] == city_to_int['Lisbon']   # day 13
    ))
    
    # Vilnius: 4 days
    vilnius_days = Sum([If(days[i] == city_to_int['Vilnius'], 1, 0) for i in range(15)])
    s.add(vilnius_days == 4)
    
    # Oslo: 3 days, with days 13-15 in Oslo
    oslo_days = Sum([If(days[i] == city_to_int['Oslo'], 1, 0) for i in range(15)])
    s.add(oslo_days == 3)
    s.add(Or(
        days[12] == city_to_int['Oslo'],  # day 13
        days[13] == city_to_int['Oslo'],  # day 14
        days[14] == city_to_int['Oslo']   # day 15
    ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        day_places = []
        
        # Get the city for each day from the model
        for i in range(15):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            day_places.append((day_num, city))
        
        # Process day_places to create the itinerary with day ranges
        current_place = day_places[0][1]
        start_day = 1
        
        for i in range(1, 15):
            day_num, city = day_places[i]
            if city != current_place:
                # Add the stay before the transition
                if start_day == day_num - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day_num-1}", "place": current_place})
                # Add the transition day (same day for both departure and arrival)
                itinerary.append({"day_range": f"Day {day_num}", "place": current_place})
                itinerary.append({"day_range": f"Day {day_num}", "place": city})
                current_place = city
                start_day = day_num
        # Add the last stay
        if start_day == 15:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-15", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))