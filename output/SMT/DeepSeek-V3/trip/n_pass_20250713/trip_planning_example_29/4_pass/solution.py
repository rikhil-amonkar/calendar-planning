from z3 import *
import json

def solve_itinerary():
    # Define the cities
    cities = ['Dubrovnik', 'Frankfurt', 'Krakow']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Create a Z3 solver
    s = Solver()
    
    # Variables: for each day (1..10), which city are we in?
    day_city = [Int(f'day_{day}_city') for day in range(1, 11)]
    for dc in day_city:
        s.add(Or([dc == city_map[city] for city in cities]))
    
    # Variables to track flight days
    flight_days = [Bool(f'flight_{day}') for day in range(1, 10)]
    
    # Constraints:
    # 1. Days 9 and 10 must be in Krakow
    s.add(day_city[8] == city_map['Krakow'])  # Day 9
    s.add(day_city[9] == city_map['Krakow'])  # Day 10
    
    # 2. Total days in each city (including flight days)
    # For each city, count days where we're in that city OR it's a flight day involving that city
    s.add(Sum([If(Or(day_city[day] == city_map['Dubrovnik'],
                    And(flight_days[day], 
                        Or(day_city[day] == city_map['Dubrovnik'], 
                           day_city[day+1] == city_map['Dubrovnik']))),
                1, 0) for day in range(9)]) + 
         If(day_city[9] == city_map['Dubrovnik'], 1, 0) == 7)  # Dubrovnik
    
    s.add(Sum([If(Or(day_city[day] == city_map['Frankfurt'],
                    And(flight_days[day],
                        Or(day_city[day] == city_map['Frankfurt'],
                           day_city[day+1] == city_map['Frankfurt']))),
                1, 0) for day in range(9)]) + 
         If(day_city[9] == city_map['Frankfurt'], 1, 0) == 3)  # Frankfurt
    
    s.add(Sum([If(Or(day_city[day] == city_map['Krakow'],
                    And(flight_days[day],
                        Or(day_city[day] == city_map['Krakow'],
                           day_city[day+1] == city_map['Krakow']))),
                1, 0) for day in range(9)]) + 
         If(day_city[9] == city_map['Krakow'], 1, 0) == 2)  # Krakow
    
    # Flight constraints: flights only between connected cities
    for day in range(9):
        s.add(Implies(flight_days[day],
                     Or(
                         And(day_city[day] == city_map['Frankfurt'], day_city[day+1] == city_map['Krakow']),
                         And(day_city[day] == city_map['Krakow'], day_city[day+1] == city_map['Frankfurt']),
                         And(day_city[day] == city_map['Dubrovnik'], day_city[day+1] == city_map['Frankfurt']),
                         And(day_city[day] == city_map['Frankfurt'], day_city[day+1] == city_map['Dubrovnik'])
                     )))
    
    # At most one flight per day
    for day in range(9):
        s.add(Implies(flight_days[day], day_city[day] != day_city[day+1]))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        day_to_city = []
        flight_days_result = []
        for day in range(10):
            city_idx = model.evaluate(day_city[day]).as_long()
            city = cities[city_idx]
            day_to_city.append((day + 1, city))  # days are 1-based
        
        for day in range(9):
            flight_days_result.append(model.evaluate(flight_days[day]))
        
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