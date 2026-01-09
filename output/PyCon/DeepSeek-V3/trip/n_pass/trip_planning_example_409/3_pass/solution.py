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
            "Zurich": (zurich, zurich + 2),
            "Helsinki": (helsinki, helsinki + 1),
            "Hamburg": (hamburg, hamburg + 1),
            "Bucharest": (bucharest, bucharest + 1),
            "Split": (split, split + 6)
        }
        
        # Check if any visit exceeds total days
        for city, (start, end) in visits.items():
            if end > total_days:
                return False
        
        # Check for overlaps
        days_used = set()
        for city, (start, end) in visits.items():
            for day in range(start, end + 1):
                if day in days_used:
                    return False
                days_used.add(day)
        
        return True
    
    problem.addConstraint(days_fit_constraint, cities)
    
    # Zurich wedding constraint: Must include days 1-3
    def zurich_constraint(zurich_start):
        zurich_end = zurich_start + 2
        return zurich_start <= 1 and zurich_end >= 3
    
    problem.addConstraint(zurich_constraint, ["Zurich"])
    
    # Split conference constraint: Must include days between 4 and 10
    def split_constraint(split_start):
        split_end = split_start + 6
        # The conference must occur between days 4-10, so it must start by day 4 and end by day 10
        return split_start <= 4 and split_end >= 10
    
    problem.addConstraint(split_constraint, ["Split"])
    
    # Flight connectivity constraint
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
    
    # Additional constraint: All visits must be consecutive (no gaps)
    def consecutive_days_constraint(zurich, helsinki, hamburg, bucharest, split):
        visits = [
            (zurich, "Zurich"),
            (helsinki, "Helsinki"),
            (hamburg, "Hamburg"), 
            (bucharest, "Bucharest"),
            (split, "Split")
        ]
        
        visits.sort()
        
        # Check if the end day of one visit equals start day of next visit minus 1
        # (accounting for travel days)
        durations = {
            "Zurich": 3,
            "Helsinki": 2,
            "Hamburg": 2,
            "Bucharest": 2,
            "Split": 7
        }
        
        for i in range(len(visits) - 1):
            current_end = visits[i][0] + durations[visits[i][1]] - 1
            next_start = visits[i + 1][0]
            
            # Allow one day gap for travel
            if next_start > current_end + 1:
                return False
        
        return True
    
    problem.addConstraint(consecutive_days_constraint, cities)
    
    # Solve the problem
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