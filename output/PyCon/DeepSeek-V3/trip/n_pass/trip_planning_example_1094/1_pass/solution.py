import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]
    
    # Define flight connections
    flights = {
        "Hamburg": ["Stockholm", "Vienna", "Barcelona", "Edinburgh", "Paris"],
        "Stockholm": ["Hamburg", "Vienna", "Edinburgh", "Krakow", "Barcelona", "Paris", "Riga"],
        "Vienna": ["Stockholm", "Hamburg", "Barcelona", "Krakow", "Riga", "Paris"],
        "Edinburgh": ["Paris", "Stockholm", "Riga", "Barcelona", "Krakow", "Hamburg"],
        "Riga": ["Barcelona", "Paris", "Stockholm", "Edinburgh", "Hamburg", "Vienna"],
        "Barcelona": ["Riga", "Krakow", "Edinburgh", "Stockholm", "Hamburg", "Vienna", "Paris"],
        "Krakow": ["Barcelona", "Stockholm", "Edinburgh", "Paris", "Vienna"],
        "Paris": ["Edinburgh", "Riga", "Krakow", "Stockholm", "Hamburg", "Barcelona", "Vienna"]
    }
    
    # Variables: start_day for each city
    # We'll use start_day and duration to calculate the schedule
    start_days = {}
    durations = {}
    
    # Fixed constraints
    durations["Vienna"] = 4
    durations["Barcelona"] = 2
    durations["Edinburgh"] = 4
    durations["Krakow"] = 3
    durations["Riga"] = 4
    durations["Hamburg"] = 2
    durations["Paris"] = 2
    durations["Stockholm"] = 2
    
    # Add variables for start days (1-16)
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, 17))
    
    # Constraint: All cities must be visited within the 16 days
    def within_schedule(*args):
        starts = {city: args[i] for i, city in enumerate(cities)}
        for city in cities:
            end_day = starts[city] + durations[city] - 1
            if end_day > 16:
                return False
        return True
    
    problem.addConstraint(within_schedule, [f"{city}_start" for city in cities])
    
    # Constraint: No overlapping visits
    def no_overlap(*args):
        starts = {city: args[i] for i, city in enumerate(cities)}
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    start1, end1 = starts[city1], starts[city1] + durations[city1] - 1
                    start2, end2 = starts[city2], starts[city2] + durations[city2] - 1
                    if not (end1 < start2 or end2 < start1):
                        return False
        return True
    
    problem.addConstraint(no_overlap, [f"{city}_start" for city in cities])
    
    # Fixed date constraints
    # Paris wedding: day 1-2
    problem.addConstraint(lambda p: p == 1, ["Paris_start"])
    
    # Hamburg conference: day 10-11  
    problem.addConstraint(lambda h: h == 10, ["Hamburg_start"])
    
    # Edinburgh friend: between day 12 and day 15
    def edinburgh_constraint(e):
        return 12 <= e <= 15 - durations["Edinburgh"] + 1
    problem.addConstraint(edinburgh_constraint, ["Edinburgh_start"])
    
    # Stockholm relatives: between day 15 and day 16
    def stockholm_constraint(s):
        return 15 <= s <= 16 - durations["Stockholm"] + 1
    problem.addConstraint(stockholm_constraint, ["Stockholm_start"])
    
    # Constraint: Travel must be via direct flights between consecutive cities
    def valid_flight_sequence(*args):
        starts = {city: args[i] for i, city in enumerate(cities)}
        
        # Create timeline of city visits
        timeline = []
        for city in cities:
            start = starts[city]
            end = start + durations[city] - 1
            timeline.append((start, end, city))
        
        timeline.sort()
        
        # Check consecutive cities in timeline are connected by flights
        for i in range(len(timeline) - 1):
            city1 = timeline[i][2]
            city2 = timeline[i + 1][2]
            if city2 not in flights[city1]:
                return False
        
        return True
    
    problem.addConstraint(valid_flight_sequence, [f"{city}_start" for city in cities])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Build the itinerary
    itinerary_entries = []
    for city in cities:
        start = solution[f"{city}_start"]
        end = start + durations[city] - 1
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_entries.append({
            "day_range": day_range,
            "place": city
        })
    
    # Sort by start day
    itinerary_entries.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    result = {"itinerary": itinerary_entries}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()