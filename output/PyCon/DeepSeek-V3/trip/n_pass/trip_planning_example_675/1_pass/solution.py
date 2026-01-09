import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    problem = Problem()
    
    # Cities and their required days
    cities = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]
    required_days = {
        "Dubrovnik": 4,
        "Split": 3,
        "Milan": 3,
        "Porto": 4,
        "Krakow": 2,
        "Munich": 5
    }
    
    # Direct flight connections
    direct_flights = [
        ("Munich", "Porto"), ("Porto", "Munich"),
        ("Split", "Milan"), ("Milan", "Split"),
        ("Milan", "Porto"), ("Porto", "Milan"),
        ("Munich", "Krakow"), ("Krakow", "Munich"),
        ("Munich", "Milan"), ("Milan", "Munich"),
        ("Dubrovnik", "Munich"), ("Munich", "Dubrovnik"),
        ("Krakow", "Split"), ("Split", "Krakow"),
        ("Krakow", "Milan"), ("Milan", "Krakow"),
        ("Munich", "Split"), ("Split", "Munich")
    ]
    
    # Special constraints
    milan_wedding_range = (11, 13)  # Must be in Milan between day 11-13
    krakow_friends_range = (8, 9)   # Must be in Krakow between day 8-9
    munich_show_range = (4, 8)      # Must be in Munich between day 4-8
    
    total_days = 16
    
    # Variables: start_day for each city
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days + 1))
        problem.addVariable(f"{city}_end", range(1, total_days + 1))
    
    # Constraint 1: End day must be after start day
    for city in cities:
        problem.addConstraint(
            lambda start, end, req=required_days[city]: end == start + req - 1,
            (f"{city}_start", f"{city}_end")
        )
    
    # Constraint 2: All city stays must be within the 16-day range
    for city in cities:
        problem.addConstraint(
            lambda start, req=required_days[city]: start + req - 1 <= total_days,
            (f"{city}_start",)
        )
    
    # Constraint 3: Cities cannot overlap in time
    for i, city1 in enumerate(cities):
        for city2 in cities[i+1:]:
            problem.addConstraint(
                lambda s1, e1, s2, e2: e1 < s2 or e2 < s1,
                (f"{city1}_start", f"{city1}_end", f"{city2}_start", f"{city2}_end")
            )
    
    # Constraint 4: Direct flight connections between consecutive cities
    def consecutive_cities_constraint(city1_end, city2_start):
        return city2_start == city1_end + 1
    
    # We need to determine the order of cities, so we'll add variables for the sequence
    problem.addVariable("city_order", [tuple(cities)])
    
    # Constraint 5: Special date constraints
    def milan_wedding_constraint(milan_start, milan_end):
        return milan_start <= milan_wedding_range[1] and milan_end >= milan_wedding_range[0]
    
    def krakow_friends_constraint(krakow_start, krakow_end):
        return krakow_start <= krakow_friends_range[1] and krakow_end >= krakow_friends_range[0]
    
    def munich_show_constraint(munich_start, munich_end):
        return munich_start <= munich_show_range[1] and munich_end >= munich_show_range[0]
    
    problem.addConstraint(milan_wedding_constraint, ("Milan_start", "Milan_end"))
    problem.addConstraint(krakow_friends_constraint, ("Krakow_start", "Krakow_end"))
    problem.addConstraint(munich_show_constraint, ("Munich_start", "Munich_end"))
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    city_stays = []
    
    for city in cities:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        city_stays.append((start, end, city))
    
    # Sort by start day
    city_stays.sort()
    
    # Create the final itinerary
    for start, end, city in city_stays:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

def main():
    try:
        result = solve_itinerary()
        print(json.dumps(result, indent=2))
    except Exception as e:
        error_result = {"error": f"Computation failed: {str(e)}"}
        print(json.dumps(error_result, indent=2))

if __name__ == "__main__":
    main()