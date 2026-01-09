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
    # We'll model this as finding start days for each city that satisfy constraints
    problem.addVariables(cities, range(1, total_days + 1))
    
    # Constraint: All cities must be visited (start days are different to ensure this)
    problem.addConstraint(AllDifferentConstraint(), cities)
    
    # Constraint: Total days must equal 12
    def total_days_constraint(zurich, helsinki, hamburg, bucharest, split):
        # Calculate end days and ensure they don't overlap incorrectly
        visits = [
            (zurich, zurich + required_days["Zurich"] - 1, "Zurich"),
            (helsinki, helsinki + required_days["Helsinki"] - 1, "Helsinki"),
            (hamburg, hamburg + required_days["Hamburg"] - 1, "Hamburg"),
            (bucharest, bucharest + required_days["Bucharest"] - 1, "Bucharest"),
            (split, split + required_days["Split"] - 1, "Split")
        ]
        
        # Check if all days from 1 to 12 are covered exactly once
        day_assignments = [0] * (total_days + 1)
        for start, end, city in visits:
            if end > total_days or start < 1:
                return False
            for day in range(start, end + 1):
                if day_assignments[day] != 0:
                    return False
                day_assignments[day] = 1
        
        # Check if all days are filled
        return sum(day_assignments[1:]) == total_days
    
    problem.addConstraint(total_days_constraint, cities)
    
    # Special constraints
    # Zurich wedding between day 1 and day 3
    def zurich_wedding_constraint(zurich):
        return zurich <= 3 and zurich + required_days["Zurich"] - 1 >= 1
    
    problem.addConstraint(zurich_wedding_constraint, ["Zurich"])
    
    # Split conference between day 4 and day 10
    def split_conference_constraint(split):
        return split <= 10 and split + required_days["Split"] - 1 >= 4
    
    problem.addConstraint(split_conference_constraint, ["Split"])
    
    # Flight connectivity constraints
    flight_routes = {
        "Zurich": ["Helsinki", "Hamburg", "Bucharest", "Split"],
        "Helsinki": ["Zurich", "Hamburg", "Split"],
        "Hamburg": ["Zurich", "Helsinki", "Bucharest", "Split"],
        "Bucharest": ["Zurich", "Hamburg"],
        "Split": ["Zurich", "Helsinki", "Hamburg"]
    }
    
    def flight_connectivity(zurich, helsinki, hamburg, bucharest, split):
        visits = [
            (zurich, zurich + required_days["Zurich"] - 1, "Zurich"),
            (helsinki, helsinki + required_days["Helsinki"] - 1, "Helsinki"),
            (hamburg, hamburg + required_days["Hamburg"] - 1, "Hamburg"),
            (bucharest, bucharest + required_days["Bucharest"] - 1, "Bucharest"),
            (split, split + required_days["Split"] - 1, "Split")
        ]
        
        visits.sort()  # Sort by start day
        
        # Check if consecutive cities are connected by direct flights
        for i in range(len(visits) - 1):
            current_city = visits[i][2]
            next_city = visits[i + 1][2]
            
            if next_city not in flight_routes[current_city]:
                return False
        
        return True
    
    problem.addConstraint(flight_connectivity, cities)
    
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