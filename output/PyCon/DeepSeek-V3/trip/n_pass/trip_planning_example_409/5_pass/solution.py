import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    problem = Problem()
    
    # Define cities and their required days
    cities = ["Zurich", "Helsinki", "Hamburg", "Bucharest", "Split"]
    required_days = {
        "Zurich": 3,
        "Helsinki": 2, 
        "Hamburg": 2,
        "Bucharest": 2,
        "Split": 7
    }
    
    total_days = 12
    
    # Create variables for start day of each city visit
    problem.addVariables(cities, range(1, total_days + 1))
    
    # Constraint: All visits must fit within the 12-day period and not overlap
    def days_fit_constraint(zurich, helsinki, hamburg, bucharest, split):
        visits = {
            "Zurich": (zurich, zurich + required_days["Zurich"] - 1),
            "Helsinki": (helsinki, helsinki + required_days["Helsinki"] - 1),
            "Hamburg": (hamburg, hamburg + required_days["Hamburg"] - 1),
            "Bucharest": (bucharest, bucharest + required_days["Bucharest"] - 1),
            "Split": (split, split + required_days["Split"] - 1)
        }
        
        # Check if any visit exceeds total days
        for city, (start, end) in visits.items():
            if end > total_days:
                return False
        
        # Check for overlaps
        for city1, (start1, end1) in visits.items():
            for city2, (start2, end2) in visits.items():
                if city1 != city2:
                    # Check if intervals overlap (inclusive of endpoints)
                    if start1 <= end2 and start2 <= end1:
                        return False
        
        return True
    
    problem.addConstraint(days_fit_constraint, cities)
    
    # Zurich wedding constraint: Must include days 1-3
    def zurich_constraint(zurich_start):
        zurich_end = zurich_start + required_days["Zurich"] - 1
        # Zurich visit must include days 1, 2, and 3
        return zurich_start <= 1 and zurich_end >= 3
    
    problem.addConstraint(zurich_constraint, ["Zurich"])
    
    # Split conference constraint: Must include days between 4 and 10
    def split_constraint(split_start):
        split_end = split_start + required_days["Split"] - 1
        # Split visit must include at least one day between 4 and 10
        return split_start <= 10 and split_end >= 4
    
    problem.addConstraint(split_constraint, ["Split"])
    
    # Flight connectivity constraint - relaxed version
    flight_routes = {
        "Zurich": ["Helsinki", "Hamburg", "Bucharest", "Split"],
        "Helsinki": ["Zurich", "Hamburg", "Split"],
        "Hamburg": ["Zurich", "Helsinki", "Bucharest", "Split"],
        "Bucharest": ["Zurich", "Hamburg"],
        "Split": ["Zurich", "Helsinki", "Hamburg"]
    }
    
    def connectivity_constraint(zurich, helsinki, hamburg, bucharest, split):
        visits = [
            (zurich, "Zurich"),
            (helsinki, "Helsinki"), 
            (hamburg, "Hamburg"),
            (bucharest, "Bucharest"),
            (split, "Split")
        ]
        
        # Sort visits by start day to get the travel sequence
        visits.sort()
        
        # Check if consecutive cities in the sequence are connected
        for i in range(len(visits) - 1):
            current_city = visits[i][1]
            next_city = visits[i + 1][1]
            
            if next_city not in flight_routes[current_city]:
                return False
        
        return True
    
    problem.addConstraint(connectivity_constraint, cities)
    
    # Additional constraint: All 12 days must be used (no gaps in the itinerary)
    def no_gaps_constraint(zurich, helsinki, hamburg, bucharest, split):
        all_days = set(range(1, total_days + 1))
        covered_days = set()
        
        visits = {
            "Zurich": range(zurich, zurich + required_days["Zurich"]),
            "Helsinki": range(helsinki, helsinki + required_days["Helsinki"]),
            "Hamburg": range(hamburg, hamburg + required_days["Hamburg"]),
            "Bucharest": range(bucharest, bucharest + required_days["Bucharest"]),
            "Split": range(split, split + required_days["Split"])
        }
        
        for days in visits.values():
            covered_days.update(days)
        
        return covered_days == all_days
    
    problem.addConstraint(no_gaps_constraint, cities)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try without the no-gaps constraint if no solution found
        problem = Problem()
        problem.addVariables(cities, range(1, total_days + 1))
        problem.addConstraint(days_fit_constraint, cities)
        problem.addConstraint(zurich_constraint, ["Zurich"])
        problem.addConstraint(split_constraint, ["Split"])
        problem.addConstraint(connectivity_constraint, cities)
        
        solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the itinerary
    visits = []
    for city in cities:
        start_day = solution[city]
        end_day = start_day + required_days[city] - 1
        visits.append((start_day, end_day, city))
    
    # Sort by start day
    visits.sort()
    
    # Create the itinerary in the required format
    itinerary = []
    for start, end, city in visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))