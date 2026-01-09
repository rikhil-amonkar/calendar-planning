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
    
    # Constraint: All visits must fit within the 12-day period
    def days_fit_constraint(*start_days):
        day_usage = [0] * (total_days + 2)  # index 0 unused, 1-12 used
        
        for i, city in enumerate(cities):
            start = start_days[i]
            end = start + required_days[city] - 1
            
            # Check if visit exceeds total days
            if end > total_days:
                return False
            
            # Check for overlaps
            for day in range(start, end + 1):
                if day_usage[day] != 0:
                    return False
                day_usage[day] = 1
        
        return True
    
    problem.addConstraint(days_fit_constraint, cities)
    
    # Zurich wedding constraint: Must include days 1-3
    def zurich_constraint(zurich_start):
        zurich_end = zurich_start + 2  # 3 days total
        return zurich_start <= 1 and zurich_end >= 3
    
    problem.addConstraint(zurich_constraint, ["Zurich"])
    
    # Split conference constraint: Must include days between 4 and 10
    def split_constraint(split_start):
        split_end = split_start + 6  # 7 days total
        return split_start <= 10 and split_end >= 4
    
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