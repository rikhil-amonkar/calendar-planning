import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = ["Dublin", "London", "Helsinki", "Reykjavik", "Mykonos", "Hamburg"]
    
    # Define variables for start days of each city visit
    # We'll use start days and durations to calculate the itinerary
    start_days = {}
    durations = {}
    
    # Fixed constraints from the problem
    durations["Mykonos"] = 3
    durations["Reykjavik"] = 2
    durations["Dublin"] = 5
    durations["London"] = 5
    durations["Helsinki"] = 4
    durations["Hamburg"] = 2
    
    # Total days constraint
    total_days = 16
    
    # Add start day variables for each city
    for city in cities:
        # Start day can be from 1 to (total_days - duration + 1)
        problem.addVariable(f"{city}_start", range(1, total_days - durations[city] + 2))
    
    # Constraint: All city visits must be within the 16-day period and not overlap in a way that violates the timeline
    # We need to ensure that the sum of durations equals total days, accounting for travel days
    
    def timeline_constraint(*starts):
        city_starts = {city: starts[i] for i, city in enumerate(cities)}
        
        # Create day assignments
        day_assignments = []
        for city in cities:
            start = city_starts[city]
            duration = durations[city]
            for day in range(start, start + duration):
                if day > total_days:
                    return False
                day_assignments.append((day, city))
        
        # Check if all days from 1 to 16 are covered exactly once
        occupied_days = set(day for day, _ in day_assignments)
        if len(occupied_days) != total_days:
            return False
        
        # Check specific constraints
        # Reykjavik wedding between day 9 and 10
        reyk_start = city_starts["Reykjavik"]
        if not (reyk_start <= 9 and reyk_start + durations["Reykjavik"] >= 10):
            return False
        
        # Dublin show from day 2 to day 6
        dublin_start = city_starts["Dublin"]
        if not (dublin_start <= 2 and dublin_start + durations["Dublin"] >= 6):
            return False
        
        # Hamburg friends between day 1 and day 2
        hamburg_start = city_starts["Hamburg"]
        if not (hamburg_start <= 1 and hamburg_start + durations["Hamburg"] >= 2):
            return False
        
        # Check flight connectivity - consecutive cities must have direct flights
        # Sort cities by start day
        sorted_cities = sorted(cities, key=lambda c: city_starts[c])
        
        for i in range(len(sorted_cities) - 1):
            city1 = sorted_cities[i]
            city2 = sorted_cities[i + 1]
            
            # Check if there's a direct flight between consecutive cities in the itinerary
            if not has_direct_flight(city1, city2):
                return False
        
        return True
    
    # Add the main constraint
    problem.addConstraint(timeline_constraint, [f"{city}_start" for city in cities])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Build the itinerary
    city_visits = []
    for city in cities:
        start = solution[f"{city}_start"]
        duration = durations[city]
        city_visits.append({
            "city": city,
            "start": start,
            "end": start + duration - 1
        })
    
    # Sort by start day
    city_visits.sort(key=lambda x: x["start"])
    
    # Create the final itinerary format
    itinerary = []
    for visit in city_visits:
        if visit["start"] == visit["end"]:
            day_range = f"Day {visit['start']}"
        else:
            day_range = f"Day {visit['start']}-{visit['end']}"
        itinerary.append({
            "day_range": day_range,
            "place": visit["city"]
        })
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

def has_direct_flight(city1, city2):
    direct_flights = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London")
    ]
    
    return (city1, city2) in direct_flights or (city2, city1) in direct_flights

if __name__ == "__main__":
    main()