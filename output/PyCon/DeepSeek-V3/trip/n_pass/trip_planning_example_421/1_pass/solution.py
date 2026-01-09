import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    required_days = {
        "Nice": 5,
        "Krakow": 6, 
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }
    
    # Direct flight connections
    connections = {
        "Nice": ["Dublin", "Frankfurt", "Lyon"],
        "Dublin": ["Nice", "Frankfurt", "Krakow", "Lyon"],
        "Frankfurt": ["Dublin", "Krakow", "Lyon", "Nice"],
        "Krakow": ["Dublin", "Frankfurt"],
        "Lyon": ["Frankfurt", "Dublin", "Nice"]
    }
    
    # Total days
    total_days = 20
    
    # Special constraints
    nice_constraint = (1, 5)  # Nice between day 1-5
    frankfurt_constraint = (19, 20)  # Frankfurt between day 19-20
    
    # Variables: order of visiting cities
    problem.addVariables(["city1", "city2", "city3", "city4", "city5"], cities)
    problem.addConstraint(AllDifferentConstraint())
    
    # Helper function to check if two cities are connected
    def are_connected(city1, city2):
        return city2 in connections.get(city1, [])
    
    # Add connection constraints between consecutive cities
    problem.addConstraint(are_connected, ["city1", "city2"])
    problem.addConstraint(are_connected, ["city2", "city3"]) 
    problem.addConstraint(are_connected, ["city3", "city4"])
    problem.addConstraint(are_connected, ["city4", "city5"])
    
    # Find all possible city sequences
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # For each city sequence, check if we can satisfy day constraints
    valid_itineraries = []
    
    for solution in solutions:
        city_sequence = [solution["city1"], solution["city2"], solution["city3"], 
                        solution["city4"], solution["city5"]]
        
        # Try to assign days to satisfy constraints
        day_assignments = {}
        current_day = 1
        
        for i, city in enumerate(city_sequence):
            days_needed = required_days[city]
            
            # Check if this is Nice (must be first and days 1-5)
            if city == "Nice" and i == 0:
                day_assignments[city] = (1, 5)
                current_day = 6
            
            # Check if this is Frankfurt (must be last and days 19-20)
            elif city == "Frankfurt" and i == 4:
                day_assignments[city] = (19, 20)
            
            else:
                # Assign consecutive days
                end_day = current_day + days_needed - 1
                if end_day > total_days:
                    break
                day_assignments[city] = (current_day, end_day)
                current_day = end_day + 1
        
        # Verify all constraints are satisfied
        if len(day_assignments) == 5:
            # Check Nice constraint
            if "Nice" in day_assignments:
                nice_start, nice_end = day_assignments["Nice"]
                if not (nice_start == 1 and nice_end == 5):
                    continue
            
            # Check Frankfurt constraint  
            if "Frankfurt" in day_assignments:
                frankfurt_start, frankfurt_end = day_assignments["Frankfurt"]
                if not (frankfurt_start == 19 and frankfurt_end == 20):
                    continue
            
            # Check total days
            total_assigned = sum(required_days[city] for city in cities)
            if total_assigned == total_days:
                valid_itineraries.append((city_sequence, day_assignments))
    
    if not valid_itineraries:
        print(json.dumps({"error": "No valid itinerary satisfying all constraints"}))
        return
    
    # Use the first valid itinerary
    city_sequence, day_assignments = valid_itineraries[0]
    
    # Build the itinerary in order
    itinerary = []
    for city in city_sequence:
        start_day, end_day = day_assignments[city]
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()