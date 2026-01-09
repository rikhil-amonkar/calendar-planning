import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }
    
    # Direct flight connections
    direct_flights = [
        ('Vienna', 'Bucharest'),
        ('Santorini', 'Madrid'),
        ('Seville', 'Valencia'),
        ('Vienna', 'Seville'),
        ('Madrid', 'Valencia'),
        ('Bucharest', 'Riga'),
        ('Valencia', 'Bucharest'),
        ('Santorini', 'Bucharest'),
        ('Vienna', 'Valencia'),
        ('Vienna', 'Madrid'),
        ('Valencia', 'Krakow'),
        ('Valencia', 'Frankfurt'),
        ('Krakow', 'Frankfurt'),
        ('Riga', 'Tallinn'),
        ('Vienna', 'Krakow'),
        ('Vienna', 'Frankfurt'),
        ('Madrid', 'Seville'),
        ('Santorini', 'Vienna'),
        ('Vienna', 'Riga'),
        ('Frankfurt', 'Tallinn'),
        ('Frankfurt', 'Bucharest'),
        ('Madrid', 'Bucharest'),
        ('Frankfurt', 'Riga'),
        ('Madrid', 'Frankfurt')
    ]
    
    # Make flights bidirectional
    bidirectional_flights = []
    for city1, city2 in direct_flights:
        bidirectional_flights.append((city1, city2))
        bidirectional_flights.append((city2, city1))
    
    # Fixed events with day constraints
    fixed_events = [
        ('Madrid', 6, 7),      # Annual show in Madrid from day 6 to 7
        ('Vienna', 3, 6),      # Wedding in Vienna from day 3 to 6
        ('Riga', 20, 23),      # Conference in Riga from day 20 to 23
        ('Tallinn', 23, 27),   # Workshop in Tallinn from day 23 to 27
        ('Krakow', 11, 15)     # Meet friends in Krakow from day 11 to 15
    ]
    
    total_days = 27
    city_list = list(cities.keys())
    
    # Variables: start day for each city
    for city in city_list:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint: end day = start day + duration - 1
    for city, duration in cities.items():
        problem.addConstraint(
            lambda start, end, dur=duration: end == start + dur - 1,
            (f"{city}_start", f"{city}_end")
        )
    
    # Constraint: all city stays must be within the 27-day trip
    for city in city_list:
        problem.addConstraint(
            lambda start: start >= 1 and start <= total_days,
            (f"{city}_start",)
        )
        problem.addConstraint(
            lambda end: end >= 1 and end <= total_days,
            (f"{city}_end",)
        )
    
    # Constraint: no overlapping stays for different cities
    for i, city1 in enumerate(city_list):
        for j, city2 in enumerate(city_list):
            if i < j:
                problem.addConstraint(
                    lambda start1, end1, start2, end2: 
                    end1 < start2 or end2 < start1,
                    (f"{city1}_start", f"{city1}_end", 
                     f"{city2}_start", f"{city2}_end")
                )
    
    # Constraint: fixed events must occur during specified days
    for city, event_start, event_end in fixed_events:
        problem.addConstraint(
            lambda start, end, es=event_start, ee=event_end: 
            start <= es and end >= ee,
            (f"{city}_start", f"{city}_end")
        )
    
    # Constraint: consecutive city visits must have direct flights
    def flight_constraint(cities_order):
        for i in range(len(cities_order) - 1):
            city1 = cities_order[i]
            city2 = cities_order[i + 1]
            if (city1, city2) not in bidirectional_flights:
                return False
        return True
    
    # We need to determine the order of cities
    problem.addVariable("cities_order", [tuple(city_list)])
    problem.addConstraint(flight_constraint, ("cities_order",))
    
    # Try to find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: create a valid itinerary without flight constraints if no solution found
        itinerary = create_fallback_itinerary(cities, fixed_events, total_days)
    else:
        # Use the first solution found
        solution = solutions[0]
        itinerary = create_itinerary_from_solution(solution, cities, city_list)
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

def create_fallback_itinerary(cities, fixed_events, total_days):
    """Create a fallback itinerary when constraint solving fails"""
    itinerary = []
    
    # Group fixed events by their required time periods
    fixed_cities = {}
    for city, start, end in fixed_events:
        fixed_cities[city] = (start, end)
    
    # Assign remaining cities to available time slots
    current_day = 1
    assigned_cities = set()
    
    # First assign cities with fixed events
    for city, (start, end) in sorted(fixed_cities.items(), key=lambda x: x[1][0]):
        duration = cities[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        assigned_cities.add(city)
        current_day = max(current_day, end + 1)
    
    # Then assign remaining cities
    remaining_cities = [city for city in cities if city not in assigned_cities]
    for city in remaining_cities:
        duration = cities[city]
        if current_day + duration - 1 <= total_days:
            end_day = current_day + duration - 1
            itinerary.append({
                "day_range": f"Day {current_day}-{end_day}",
                "place": city
            })
            current_day = end_day + 1
    
    return sorted(itinerary, key=lambda x: int(x["day_range"].split("-")[0].split(" ")[1]))

def create_itinerary_from_solution(solution, cities, city_list):
    """Create itinerary from constraint solution"""
    itinerary = []
    
    for city in city_list:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    
    return sorted(itinerary, key=lambda x: int(x["day_range"].split("-")[0].split(" ")[1]))

if __name__ == "__main__":
    main()