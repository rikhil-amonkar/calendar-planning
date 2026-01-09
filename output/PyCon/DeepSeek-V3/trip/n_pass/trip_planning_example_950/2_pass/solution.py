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
    
    # Constraint 1: End day = Start day + required days - 1
    # We'll calculate this later
    
    # Constraint 2: All stays must be within the 17-day period
    for city in cities:
        problem.addConstraint(
            lambda start, req=required_days[city]: start + req - 1 <= total_days,
            [f"{city}_start"]
        )
    
    # Constraint 3: No overlapping stays (allow travel days)
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:
                def no_overlap(s1, s2, req1=required_days[city1], req2=required_days[city2]):
                    e1 = s1 + req1 - 1
                    e2 = s2 + req2 - 1
                    # Allow one day gap for travel
                    return e1 + 1 < s2 or e2 + 1 < s1
                problem.addConstraint(no_overlap, [f"{city1}_start", f"{city2}_start"])
    
    # Constraint 4: Fixed events
    # Mykonos wedding between day 4 and 6 - must include at least one of these days
    problem.addConstraint(
        lambda start: start <= 4 and start + 2 >= 4,  # 3-day stay covering day 4-6
        ["Mykonos_start"]
    )
    
    # Rome conference during day 1-4 - must include at least day 1-4
    problem.addConstraint(
        lambda start: start <= 1 and start + 3 >= 4,  # 4-day stay covering day 1-4
        ["Rome_start"]
    )
    
    # Krakow show day 16-17 - must include both days
    problem.addConstraint(
        lambda start: start <= 16 and start + 1 >= 17,  # 2-day stay covering day 16-17
        ["Krakow_start"]
    )
    
    # Constraint 5: Flight connections between consecutive cities
    # We'll order the cities by start day and check connections
    def check_flight_connections(*starts):
        # Create list of (start_day, city, required_days)
        city_visits = [(starts[i], cities[i], required_days[cities[i]]) for i in range(len(cities))]
        
        # Sort by start day
        city_visits.sort()
        
        # Check consecutive cities in timeline are connected
        for i in range(len(city_visits) - 1):
            current_city = city_visits[i][1]
            next_city = city_visits[i + 1][1]
            
            # Check if there's a direct flight connection
            if next_city not in connections.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(check_flight_connections, [f"{city}_start" for city in cities])
    
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
        end = start + required_days[city] - 1
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