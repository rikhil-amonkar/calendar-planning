from z3 import *
import json

def solve_scheduling_problem():
    # Cities and direct flights
    cities = ['Dublin', 'Krakow', 'Istanbul', 'Venice', 'Naples', 'Brussels', 'Mykonos', 'Frankfurt']
    direct_flights = {
        'Dublin': ['Brussels', 'Naples', 'Krakow', 'Frankfurt', 'Istanbul', 'Venice'],
        'Brussels': ['Dublin', 'Krakow', 'Naples', 'Istanbul', 'Frankfurt', 'Venice'],
        'Mykonos': ['Naples'],
        'Naples': ['Mykonos', 'Dublin', 'Istanbul', 'Brussels', 'Venice', 'Frankfurt'],
        'Venice': ['Istanbul', 'Frankfurt', 'Brussels', 'Naples', 'Dublin'],
        'Istanbul': ['Venice', 'Frankfurt', 'Krakow', 'Brussels', 'Naples', 'Dublin'],
        'Frankfurt': ['Krakow', 'Istanbul', 'Brussels', 'Venice', 'Naples', 'Dublin'],
        'Krakow': ['Frankfurt', 'Brussels', 'Istanbul', 'Dublin']
    }
    
    # Initialize solver
    s = Solver()
    num_days = 21
    days = range(1, num_days + 1)
    
    # City mapping
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}
    
    # Day-city assignment variables
    day_city = {day: Int(f"day_{day}_city") for day in days}
    
    # Each day must be assigned to a valid city
    for day in days:
        s.add(Or([day_city[day] == city_to_int[city] for city in cities]))
    
    # Fixed stays
    # Dublin days 11-15 (5 days total)
    for day in range(11, 16):
        s.add(day_city[day] == city_to_int['Dublin'])
    
    # Mykonos days 1-4 (4 days)
    for day in range(1, 5):
        s.add(day_city[day] == city_to_int['Mykonos'])
    
    # Istanbul: 3 days total with at least 1 day between 9-11
    s.add(Sum([If(day_city[day] == city_to_int['Istanbul'], 1, 0) for day in days]) == 3)
    s.add(Or([day_city[day] == city_to_int['Istanbul'] for day in range(9, 12)]))
    
    # Other city durations
    s.add(Sum([If(day_city[day] == city_to_int['Krakow'], 1, 0) for day in days]) == 4)
    s.add(Sum([If(day_city[day] == city_to_int['Venice'], 1, 0) for day in days]) == 3)
    s.add(Sum([If(day_city[day] == city_to_int['Naples'], 1, 0) for day in days]) == 4)
    s.add(Sum([If(day_city[day] == city_to_int['Brussels'], 1, 0) for day in days]) == 2)
    s.add(Sum([If(day_city[day] == city_to_int['Frankfurt'], 1, 0) for day in days]) == 3)
    s.add(Or([day_city[day] == city_to_int['Frankfurt'] for day in range(15, 18)]))
    
    # Flight constraints
    for day in range(1, num_days):
        current = day_city[day]
        next_day = day_city[day + 1]
        s.add(Implies(current != next_day, 
                     Or([And(current == city_to_int[a], next_day == city_to_int[b]) 
                         for a in cities for b in direct_flights[a]])))
    
    # Solve and format output
    if s.check() == sat:
        model = s.model()
        schedule = []
        current_city = None
        start_day = 1
        
        for day in days:
            city_idx = model.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            
            if city != current_city:
                if current_city is not None:
                    if start_day == day - 1:
                        schedule.append({"day_range": f"Day {start_day}", "place": current_city})
                    else:
                        schedule.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                
                schedule.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day
        
        # Add last stay
        if start_day == num_days:
            schedule.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            schedule.append({"day_range": f"Day {start_day}-{num_days}", "place": current_city})
        
        # Handle flight days
        final_schedule = []
        for i in range(len(schedule)):
            entry = schedule[i]
            day_range = entry["day_range"]
            place = entry["place"]
            
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                for day in range(start, end + 1):
                    final_schedule.append({"day_range": f"Day {day}", "place": place})
            else:
                day = int(day_range.replace('Day ', ''))
                final_schedule.append({"day_range": f"Day {day}", "place": place})
        
        # Group consecutive days
        grouped = []
        i = 0
        while i < len(final_schedule):
            current = final_schedule[i]
            day = int(current["day_range"].replace('Day ', ''))
            place = current["place"]
            j = i + 1
            
            while j < len(final_schedule):
                next_entry = final_schedule[j]
                next_day = int(next_entry["day_range"].replace('Day ', ''))
                next_place = next_entry["place"]
                
                if next_day == day + (j - i) and next_place == place:
                    j += 1
                else:
                    break
            
            if j - i == 1:
                grouped.append({"day_range": f"Day {day}", "place": place})
            else:
                grouped.append({"day_range": f"Day {day}-{day + (j - i) - 1}", "place": place})
            i = j
        
        print(json.dumps({"itinerary": grouped}, indent=2))
    else:
        print("No solution found")

solve_scheduling_problem()