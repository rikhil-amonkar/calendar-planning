import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}

    # Direct flights (bidirectional)
    direct_flights = [
        ('Vienna', 'Milan'),
        ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'),
        ('Vienna', 'Riga'),
        ('Vienna', 'Rome'),
        ('Vienna', 'Oslo'),
        ('Milan', 'Riga'),
        ('Milan', 'Oslo'),
        ('Milan', 'Lisbon'),
        ('Milan', 'Vilnius'),
        ('Rome', 'Oslo'),
        ('Rome', 'Riga'),
        ('Rome', 'Lisbon'),
        ('Riga', 'Oslo'),
        ('Riga', 'Vilnius'),
        ('Riga', 'Lisbon'),
        ('Lisbon', 'Oslo'),
        ('Vilnius', 'Oslo')
    ]

    # Create flight connections dictionary
    flight_connections = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_connections[a].add(b)
        flight_connections[b].add(a)

    # Create solver
    s = Solver()

    # Day variables: day[i] is the city on day i (1-based)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    # Add constraints for each day to be a valid city
    for day in days:
        s.add(day >= 0, day < len(cities))

    # Fixed constraints
    s.add(days[0] == city_to_int['Vienna'])  # Day 1 in Vienna
    s.add(days[3] == city_to_int['Vienna'])  # Day 4 in Vienna

    # Flight constraints between consecutive days
    for i in range(14):
        current_city = days[i]
        next_city = days[i+1]
        s.add(Or(
            current_city == next_city,  # Stay in same city
            *[And(current_city == city_to_int[a], next_city == city_to_int[b]) 
              for a in flight_connections for b in flight_connections[a]]
        ))

    # Duration constraints
    def count_days(city):
        return Sum([If(days[i] == city_to_int[city], 1, 0) for i in range(15)])

    s.add(count_days('Vienna') == 4)
    s.add(count_days('Milan') == 2)
    s.add(count_days('Rome') == 3)
    s.add(count_days('Riga') == 2)
    s.add(count_days('Lisbon') == 3)
    s.add(count_days('Vilnius') == 4)
    s.add(count_days('Oslo') == 3)

    # Lisbon between days 11-13
    s.add(Or(
        days[10] == city_to_int['Lisbon'],  # Day 11
        days[11] == city_to_int['Lisbon'],  # Day 12
        days[12] == city_to_int['Lisbon']   # Day 13
    ))

    # Oslo between days 13-15
    s.add(Or(
        days[12] == city_to_int['Oslo'],  # Day 13
        days[13] == city_to_int['Oslo'],  # Day 14
        days[14] == city_to_int['Oslo']   # Day 15
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