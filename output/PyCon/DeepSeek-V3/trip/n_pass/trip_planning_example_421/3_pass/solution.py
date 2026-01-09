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
    
    # We need to assign both position in sequence and start day for each city
    # Let's use variables: pos_0, pos_1, ... for sequence position
    # and start_0, start_1, ... for start day
    
    # Create variables for each city's position and start day
    positions = list(range(5))  # 0 to 4 for the 5 positions in sequence
    problem.addVariables([f"pos_{i}" for i in positions], positions)
    problem.addVariables([f"start_{city}" for city in cities], range(1, total_days + 1))
    
    # All cities must have unique positions
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{i}" for i in positions])
    
    # All start days must lead to non-overlapping stays
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:
                # Either city1 ends before city2 starts, or city2 ends before city1 starts
                def no_overlap(start1, start2, c1=city1, c2=city2):
                    end1 = start1 + required_days[c1] - 1
                    end2 = start2 + required_days[c2] - 1
                    return end1 < start2 or end2 < start1
                problem.addConstraint(no_overlap, [f"start_{city1}", f"start_{city2}"])
    
    # Connection constraints between consecutive cities in sequence
    for pos in range(4):
        def connected_constraint(*args, pos=pos):
            # args will be the cities at positions 0 through 4
            city1 = args[pos]
            city2 = args[pos + 1]
            return city2 in connections.get(city1, [])
        problem.addConstraint(connected_constraint, [f"pos_{i}" for i in positions])
    
    # Nice must be between day 1-5 (so start day must be 1)
    problem.addConstraint(lambda start: start == 1, ["start_Nice"])
    
    # Frankfurt must be between day 19-20 (so start day must be 19)
    problem.addConstraint(lambda start: start == 19, ["start_Frankfurt"])
    
    # All stays must fit within the 20-day period
    for city in cities:
        def within_period(start, city=city):
            return start + required_days[city] - 1 <= total_days
        problem.addConstraint(within_period, [f"start_{city}"])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary satisfying all constraints"}))
        return
    
    # Convert the first solution to a readable itinerary
    sol = solutions[0]
    
    # Create a mapping from position to city
    pos_to_city = {}
    for i in positions:
        city_at_pos = sol[f"pos_{i}"]
        # Find which city has this position
        for city in cities:
            if sol[f"pos_{city}"] == i:
                pos_to_city[i] = city
                break
    
    # Build the sequence in order
    sequence = [pos_to_city[i] for i in sorted(positions)]
    
    # Build the itinerary
    itinerary = []
    for city in sequence:
        start_day = sol[f"start_{city}"]
        end_day = start_day + required_days[city] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()