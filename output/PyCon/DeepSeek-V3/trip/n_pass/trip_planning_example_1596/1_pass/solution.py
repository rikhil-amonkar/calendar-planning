import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = [
        "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw", 
        "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
    ]
    
    # Define the flight connections as a dictionary
    flights = {
        "Budapest": ["Munich", "Vienna", "Edinburgh", "Barcelona", "Warsaw", "Bucharest"],
        "Bucharest": ["Riga", "Munich", "Warsaw", "Vienna", "Budapest", "Barcelona"],
        "Munich": ["Budapest", "Krakow", "Warsaw", "Bucharest", "Barcelona", "Stockholm", "Edinburgh", "Vienna"],
        "Krakow": ["Munich", "Warsaw", "Edinburgh", "Stockholm", "Vienna", "Barcelona"],
        "Barcelona": ["Warsaw", "Munich", "Stockholm", "Riga", "Edinburgh", "Budapest", "Bucharest", "Krakow", "Vienna"],
        "Warsaw": ["Munich", "Barcelona", "Bucharest", "Budapest", "Vienna", "Riga", "Stockholm", "Krakow"],
        "Stockholm": ["Edinburgh", "Krakow", "Munich", "Barcelona", "Riga", "Warsaw", "Vienna"],
        "Riga": ["Bucharest", "Barcelona", "Edinburgh", "Vienna", "Warsaw", "Stockholm", "Munich"],
        "Edinburgh": ["Stockholm", "Krakow", "Budapest", "Barcelona", "Munich", "Riga"],
        "Vienna": ["Budapest", "Riga", "Krakow", "Bucharest", "Munich", "Stockholm", "Warsaw", "Barcelona"]
    }
    
    # Required days for each city
    required_days = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }
    
    # Fixed events with day ranges
    fixed_events = [
        {"city": "Munich", "start": 18, "end": 20},
        {"city": "Warsaw", "start": 25, "end": 29},
        {"city": "Budapest", "start": 9, "end": 13},
        {"city": "Stockholm", "start": 17, "end": 18},
        {"city": "Edinburgh", "start": 1, "end": 5}
    ]
    
    total_days = 32
    
    # Create variables for start day of each city visit
    # We'll model this as a sequence of city visits with start days
    # Since we have fixed events, we need to ensure those cities are visited during those days
    
    # First, let's create a list of all city visits we need to schedule
    # Each city appears once with its required duration
    city_visits = []
    for city in cities:
        city_visits.append({"city": city, "duration": required_days[city]})
    
    # We need to assign start days to each city visit
    # But we also need to ensure the sequence makes sense with flight connections
    
    # This is a complex constraint satisfaction problem
    # Let's try a simpler approach: create a day-by-day itinerary
    
    # Initialize variables for each day (1-32)
    day_vars = [f"day_{i}" for i in range(1, total_days + 1)]
    problem.addVariables(day_vars, cities)
    
    # Constraint: Fixed events must happen on specific days
    for event in fixed_events:
        city = event["city"]
        start = event["start"]
        end = event["end"]
        for day in range(start, end + 1):
            problem.addConstraint(lambda x, c=city: x == c, [f"day_{day}"])
    
    # Constraint: Each city must be visited for exactly the required number of days
    for city in cities:
        problem.addConstraint(lambda *days, c=city, req=required_days[city]: 
                             sum(1 for day in days if day == c) == req, 
                             day_vars)
    
    # Constraint: Consecutive days in the same city must form contiguous blocks
    # This is complex to model directly, so we'll use a simpler approach
    # We'll ensure that if you're in a city on day i, you can only be in connected cities on day i+1
    
    for i in range(1, total_days):
        problem.addConstraint(
            lambda city_today, city_tomorrow, flights=flights: 
            city_today == city_tomorrow or city_tomorrow in flights[city_today],
            [f"day_{i}", f"day_{i+1}"]
        )
    
    # Find a solution
    solution = problem.getSolution()
    
    if solution:
        # Convert solution to itinerary format
        itinerary = []
        current_city = solution["day_1"]
        start_day = 1
        
        for day in range(2, total_days + 1):
            if solution[f"day_{day}"] != current_city:
                # End of stay in current city
                itinerary.append({
                    "day_range": f"Day {start_day}-{day-1}",
                    "place": current_city
                })
                current_city = solution[f"day_{day}"]
                start_day = day
        
        # Add the last stay
        itinerary.append({
            "day_range": f"Day {start_day}-{total_days}",
            "place": current_city
        })
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        # If no solution found with the strict constraints, try a fallback approach
        print(json.dumps({"itinerary": [{"day_range": "No valid itinerary found", "place": "Please check constraints"}]}, indent=2))

if __name__ == "__main__":
    main()