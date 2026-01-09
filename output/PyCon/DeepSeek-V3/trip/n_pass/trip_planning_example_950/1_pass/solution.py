from constraint import Problem
import json

def solve_itinerary():
    problem = Problem()
    
    # Cities and their required days
    cities = ["Mykonos", "Riga", "Munich", "Bucharest", "Rome", "Nice", "Krakow"]
    required_days = {
        "Mykonos": 3,
        "Riga": 3, 
        "Munich": 4,
        "Bucharest": 4,
        "Rome": 4,
        "Nice": 3,
        "Krakow": 2
    }
    
    # Direct flight connections
    connections = {
        "Nice": ["Riga", "Rome", "Mykonos", "Munich"],
        "Riga": ["Nice", "Bucharest", "Munich", "Rome"],
        "Bucharest": ["Munich", "Riga", "Rome"],
        "Munich": ["Bucharest", "Mykonos", "Rome", "Nice", "Krakow", "Riga"],
        "Rome": ["Nice", "Munich", "Mykonos", "Bucharest", "Riga"],
        "Mykonos": ["Munich", "Nice", "Rome"],
        "Krakow": ["Munich"]
    }
    
    # Fixed constraints
    total_days = 17
    
    # Define variables: start day for each city
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint 1: End day = Start day + required days - 1
    for city in cities:
        def end_day_constraint(start, end, req_days=required_days[city]):
            return end == start + req_days - 1
        problem.addConstraint(end_day_constraint, [f"{city}_start", f"{city}_end"])
    
    # Constraint 2: All stays must be within the 17-day period
    for city in cities:
        problem.addConstraint(lambda start, end: start >= 1 and end <= total_days, 
                            [f"{city}_start", f"{city}_end"])
    
    # Constraint 3: No overlapping stays for different cities
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:
                def no_overlap(s1, e1, s2, e2):
                    return e1 < s2 or e2 < s1
                problem.addConstraint(no_overlap, 
                                    [f"{city1}_start", f"{city1}_end", 
                                     f"{city2}_start", f"{city2}_end"])
    
    # Constraint 4: Fixed events
    # Mykonos wedding between day 4 and 6
    problem.addConstraint(lambda start, end: start <= 4 and end >= 6, 
                        ["Mykonos_start", "Mykonos_end"])
    
    # Rome conference during day 1-4
    problem.addConstraint(lambda start, end: start <= 1 and end >= 4, 
                        ["Rome_start", "Rome_end"])
    
    # Krakow show day 16-17
    problem.addConstraint(lambda start, end: start <= 16 and end >= 17, 
                        ["Krakow_start", "Krakow_end"])
    
    # Constraint 5: Flight connections between consecutive cities
    city_vars = [f"{city}_start" for city in cities] + [f"{city}_end" for city in cities]
    
    def flight_connections(*args):
        # Extract start and end days for all cities
        starts = {city: args[i] for i, city in enumerate(cities)}
        ends = {city: args[i + len(cities)] for i, city in enumerate(cities)}
        
        # Create timeline of city visits
        timeline = []
        for city in cities:
            timeline.append((starts[city], city, "start"))
            timeline.append((ends[city], city, "end"))
        
        timeline.sort()
        
        # Check consecutive cities are connected by flights
        current_cities = set()
        previous_cities = set()
        
        for day, city, event_type in timeline:
            if event_type == "start":
                current_cities.add(city)
            else:
                current_cities.remove(city)
            
            # When we have a transition (city leaves and new city arrives)
            if previous_cities and current_cities and previous_cities != current_cities:
                # Check if there's a flight connection between the leaving and arriving cities
                leaving_city = list(previous_cities - current_cities)[0] if previous_cities - current_cities else None
                arriving_city = list(current_cities - previous_cities)[0] if current_cities - previous_cities else None
                
                if leaving_city and arriving_city:
                    if arriving_city not in connections.get(leaving_city, []):
                        return False
            
            previous_cities = current_cities.copy()
        
        return True
    
    problem.addConstraint(flight_connections, city_vars)
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    for city in cities:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Sort by start day
    itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))