from z3 import *
import json

def solve_itinerary():
    # Define the cities
    cities = ['Dubrovnik', 'Frankfurt', 'Krakow']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections
    connections = [
        ('Frankfurt', 'Krakow'),
        ('Dubrovnik', 'Frankfurt')
    ]
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: for each day (1..10), which city are we in?
    day_city = [Int(f'day_{day}_city') for day in range(1, 11)]
    for dc in day_city:
        s.add(Or([dc == city_map[city] for city in cities]))
    
    # Constraints:
    # 1. Total days in Dubrovnik = 7
    s.add(Sum([If(day_city[day] == city_map['Dubrovnik'], 1, 0) for day in range(10)]) == 7)
    # 2. Total days in Frankfurt = 3
    s.add(Sum([If(day_city[day] == city_map['Frankfurt'], 1, 0) for day in range(10)]) == 3)
    # 3. Days 9 and 10 must be in Krakow
    s.add(day_city[8] == city_map['Krakow'])  # Day 9 is index 8 (0-based)
    s.add(day_city[9] == city_map['Krakow'])  # Day 10 is index 9
    
    # Flight constraints: transitions between days must be via direct flights
    for prev_day in range(9):  # days 1-9 (since next day is day+1)
        current_city = day_city[prev_day]
        next_city = day_city[prev_day + 1]
        # Either stay in the same city, or move to a connected city
        s.add(Or(
            current_city == next_city,
            And(
                Or(
                    And(current_city == city_map['Frankfurt'], next_city == city_map['Krakow']),
                    And(current_city == city_map['Krakow'], next_city == city_map['Frankfurt']),
                    And(current_city == city_map['Dubrovnik'], next_city == city_map['Frankfurt']),
                    And(current_city == city_map['Frankfurt'], next_city == city_map['Dubrovnik'])
                )
            )
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        day_to_city = []
        for day in range(10):
            city_idx = model.evaluate(day_city[day]).as_long()
            city = cities[city_idx]
            day_to_city.append((day + 1, city))  # days are 1-based
        
        # Generate the itinerary
        itinerary = []
        current_place = day_to_city[0][1]
        start_day = 1
        
        for day in range(1, 10):
            day_num = day + 1
            if day_to_city[day][1] != current_place:
                # City change on day_num
                # Add the stay up to day_num-1 if start_day < day_num
                if start_day < day_num:
                    itinerary.append({'day_range': f'Day {start_day}-{day_num - 1}', 'place': current_place})
                # Add the departure and arrival for the flight day
                itinerary.append({'day_range': f'Day {day_num}', 'place': current_place})
                itinerary.append({'day_range': f'Day {day_num}', 'place': day_to_city[day][1]})
                # Update current_place and start_day
                current_place = day_to_city[day][1]
                start_day = day_num
        # Add the last segment
        if start_day <= 10:
            if start_day == 10:
                itinerary.append({'day_range': f'Day {start_day}', 'place': current_place})
            else:
                itinerary.append({'day_range': f'Day {start_day}-10', 'place': current_place})
        
        # Prepare the output
        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))