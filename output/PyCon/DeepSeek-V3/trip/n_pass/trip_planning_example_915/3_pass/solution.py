import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    problem = Problem()
    
    cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
    
    # Define variables for start days of each city visit
    days_total = 26
    
    # Fixed constraints from the problem
    bucharest_days = 3
    venice_days = 5
    prague_days = 4
    frankfurt_days = 5
    zurich_days = 5
    florence_days = 5
    tallinn_days = 5
    
    # Add variables for start days
    problem.addVariable('bucharest_start', range(1, days_total - bucharest_days + 2))
    problem.addVariable('venice_start', range(1, days_total - venice_days + 2))
    problem.addVariable('prague_start', range(1, days_total - prague_days + 2))
    problem.addVariable('frankfurt_start', range(1, days_total - frankfurt_days + 2))
    problem.addVariable('zurich_start', range(1, days_total - zurich_days + 2))
    problem.addVariable('florence_start', range(1, days_total - florence_days + 2))
    problem.addVariable('tallinn_start', range(1, days_total - tallinn_days + 2))
    
    # Fixed date constraints
    def venice_wedding_constraint(v_start):
        # Venice wedding between day 22 and 26, so Venice visit must include these days
        return v_start <= 22 and (v_start + venice_days - 1) >= 22
    
    def frankfurt_show_constraint(f_start):
        # Frankfurt show between day 12 and 16
        return f_start <= 12 and (f_start + frankfurt_days - 1) >= 16
    
    def tallinn_friends_constraint(t_start):
        # Tallinn friends between day 8 and 12
        return t_start <= 8 and (t_start + tallinn_days - 1) >= 12
    
    problem.addConstraint(venice_wedding_constraint, ['venice_start'])
    problem.addConstraint(frankfurt_show_constraint, ['frankfurt_start'])
    problem.addConstraint(tallinn_friends_constraint, ['tallinn_start'])
    
    # No overlap constraint - ensure cities don't overlap in time
    def no_overlap(city1_start, city2_start, city1_days, city2_days):
        city1_end = city1_start + city1_days - 1
        city2_end = city2_start + city2_days - 1
        return (city1_end < city2_start) or (city2_end < city1_start)
    
    # Add no-overlap constraints for all city pairs with proper duration handling
    city_info = {
        'bucharest_start': bucharest_days,
        'venice_start': venice_days,
        'prague_start': prague_days,
        'frankfurt_start': frankfurt_days,
        'zurich_start': zurich_days,
        'florence_start': florence_days,
        'tallinn_start': tallinn_days
    }
    
    city_vars = list(city_info.keys())
    for i in range(len(city_vars)):
        for j in range(i + 1, len(city_vars)):
            var1 = city_vars[i]
            var2 = city_vars[j]
            days1 = city_info[var1]
            days2 = city_info[var2]
            
            # Create a lambda that captures the durations
            problem.addConstraint(
                lambda s1, s2, d1=days1, d2=days2: no_overlap(s1, s2, d1, d2),
                [var1, var2]
            )
    
    # Flight connectivity constraints
    direct_flights = [
        ('Prague', 'Tallinn'), ('Prague', 'Zurich'), ('Florence', 'Prague'),
        ('Frankfurt', 'Bucharest'), ('Frankfurt', 'Venice'), ('Prague', 'Bucharest'),
        ('Bucharest', 'Zurich'), ('Tallinn', 'Frankfurt'), ('Zurich', 'Florence'),
        ('Frankfurt', 'Zurich'), ('Zurich', 'Venice'), ('Florence', 'Frankfurt'),
        ('Prague', 'Frankfurt'), ('Tallinn', 'Zurich')
    ]
    
    # Convert city names to variable names
    city_to_var = {
        'Bucharest': 'bucharest_start',
        'Venice': 'venice_start', 
        'Prague': 'prague_start',
        'Frankfurt': 'frankfurt_start',
        'Zurich': 'zurich_start',
        'Florence': 'florence_start',
        'Tallinn': 'tallinn_start'
    }
    
    city_durations = {
        'Bucharest': bucharest_days,
        'Venice': venice_days,
        'Prague': prague_days,
        'Frankfurt': frankfurt_days,
        'Zurich': zurich_days,
        'Florence': florence_days,
        'Tallinn': tallinn_days
    }
    
    def can_travel_between(city1_start, city2_start, city1_days, city2_days):
        city1_end = city1_start + city1_days - 1
        city2_end = city2_start + city2_days - 1
        
        # Check if cities are consecutive in itinerary (one ends right before the other starts)
        return (city1_end + 1 == city2_start) or (city2_end + 1 == city1_start)
    
    # Add flight connectivity constraints for consecutive cities
    for flight in direct_flights:
        city1, city2 = flight
        var1 = city_to_var[city1]
        var2 = city_to_var[city2]
        days1 = city_durations[city1]
        days2 = city_durations[city2]
        
        problem.addConstraint(
            lambda start1, start2, d1=days1, d2=days2: can_travel_between(start1, start2, d1, d2),
            [var1, var2]
        )
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Create itinerary list
    itinerary = []
    city_visits = []
    
    for city, var_name in city_to_var.items():
        start_day = solution[var_name]
        duration = city_durations[city]
        end_day = start_day + duration - 1
        city_visits.append({
            'city': city,
            'start': start_day,
            'end': end_day,
            'duration': duration
        })
    
    # Sort by start day
    city_visits.sort(key=lambda x: x['start'])
    
    # Build final itinerary
    for visit in city_visits:
        day_range = f"Day {visit['start']}-{visit['end']}"
        itinerary.append({
            "day_range": day_range,
            "place": visit['city']
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))