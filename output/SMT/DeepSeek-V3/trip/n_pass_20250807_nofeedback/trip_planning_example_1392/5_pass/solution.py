import json
from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    city_vars = {city: [Bool(f"{city}_{day}") for day in range(1, 25)] for city in cities}
    
    s = Solver()
    
    # Enhanced direct flight connections with proper city names
    direct_flights = {
        'Venice': ['Nice', 'Amsterdam', 'Stuttgart', 'Naples', 'Barcelona'],
        'Naples': ['Amsterdam', 'Split', 'Nice', 'Valencia', 'Barcelona', 'Venice', 'Stuttgart', 'Porto'],
        'Valencia': ['Stuttgart', 'Amsterdam', 'Naples', 'Barcelona', 'Porto'],
        'Stuttgart': ['Valencia', 'Porto', 'Split', 'Amsterdam', 'Naples', 'Venice', 'Barcelona'],
        'Split': ['Stuttgart', 'Naples', 'Amsterdam', 'Barcelona'],
        'Amsterdam': ['Naples', 'Nice', 'Valencia', 'Venice', 'Split', 'Barcelona', 'Stuttgart', 'Porto'],
        'Nice': ['Venice', 'Barcelona', 'Amsterdam', 'Naples', 'Porto'],
        'Barcelona': ['Nice', 'Porto', 'Valencia', 'Naples', 'Split', 'Amsterdam', 'Venice', 'Stuttgart'],
        'Porto': ['Stuttgart', 'Nice', 'Barcelona', 'Amsterdam', 'Valencia']
    }
    
    # Each day must be in exactly one city
    for day in range(1, 25):
        s.add(Or([city_vars[city][day-1] for city in cities]))
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    s.add(Implies(And(city_vars[city1][day-1], city_vars[city2][day]), city2 in direct_flights[city1]))
    
    # Duration constraints with minimum consecutive stays
    def add_duration_constraint(city, days):
        # Create a variable for each possible start day of the stay
        starts = [Bool(f"start_{city}_{d}") for d in range(24 - days + 1)]
        s.add(Or(starts))
        for d in range(24 - days + 1):
            # If this is a start day, enforce consecutive days
            s.add(Implies(starts[d], And([city_vars[city][d + i] for i in range(days)])))
    
    add_duration_constraint('Valencia', 5)
    add_duration_constraint('Split', 5)
    add_duration_constraint('Venice', 5)
    add_duration_constraint('Porto', 4)
    add_duration_constraint('Amsterdam', 4)
    add_duration_constraint('Naples', 3)
    add_duration_constraint('Stuttgart', 2)
    add_duration_constraint('Nice', 2)
    add_duration_constraint('Barcelona', 2)
    
    # Special date constraints
    # Venice conference days 6-10
    for day in range(5, 10):
        s.add(city_vars['Venice'][day])
    
    # Barcelona workshop days 5-6
    s.add(Or(city_vars['Barcelona'][4], city_vars['Barcelona'][5]))
    
    # Naples meeting days 18-20
    s.add(Or([city_vars['Naples'][d] for d in range(17, 20)]))
    
    # Nice meeting days 23-24
    s.add(Or(city_vars['Nice'][22], city_vars['Nice'][23]))
    
    # Ensure no single-day stays except for transitions
    for city in cities:
        for day in range(1, 24):
            s.add(Implies(And(city_vars[city][day-1], Not(city_vars[city][day])), 
                        Or([city_vars[city][day+1] for city2 in cities if city2 in direct_flights[city]])))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        for day in range(1, 25):
            for city in cities:
                if is_true(model[city_vars[city][day-1]]):
                    if city != current_city:
                        if current_city is not None:
                            itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_city})
                        current_city = city
                        start_day = day
                    break
        itinerary.append({'day_range': f'Day {start_day}-24', 'place': current_city})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            start, end = map(int, entry['day_range'].split('-')[0][4:]), map(int, entry['day_range'].split('-')[1][4:])
            city_days[entry['place']] += end - start + 1
        
        for city, days in city_days.items():
            if city == 'Naples' and days != 3:
                return {"error": "Naples duration constraint violated"}
            if city == 'Valencia' and days != 5:
                return {"error": "Valencia duration constraint violated"}
            if city == 'Stuttgart' and days != 2:
                return {"error": "Stuttgart duration constraint violated"}
            if city == 'Split' and days != 5:
                return {"error": "Split duration constraint violated"}
            if city == 'Venice' and days != 5:
                return {"error": "Venice duration constraint violated"}
            if city == 'Amsterdam' and days != 4:
                return {"error": "Amsterdam duration constraint violated"}
            if city == 'Nice' and days != 2:
                return {"error": "Nice duration constraint violated"}
            if city == 'Barcelona' and days != 2:
                return {"error": "Barcelona duration constraint violated"}
            if city == 'Porto' and days != 4:
                return {"error": "Porto duration constraint violated"}
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))